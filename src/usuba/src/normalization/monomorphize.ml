open Usuba_AST
open Basic_utils
open Utils

let compact = ref false

(* Will be used within Hslice/Vslice/Bslice (which is why it's located
   up here) *)
let rec specialize_typ (env_dir:(dir,dir) Hashtbl.t)
                       (env_m:(mtyp,mtyp) Hashtbl.t)
                       (t:typ) : typ =
  match t with
  | Nat -> t
  | Array(t', n)  -> Array(specialize_typ env_dir env_m t', n)
  | Uint(d, m, n) -> match Hashtbl.find_opt env_dir d, Hashtbl.find_opt env_m m with
                     | Some d', Some m' -> Uint(d', m', n)
                     | Some d', None    -> Uint(d', m,  n)
                     | None,    Some m' -> Uint(d,  m', n)
                     | None,    None    -> Uint(d,  m,  n)

module HVsliceCommon = struct

  let specialize_typ (d:dir) (m:mtyp) (n:int) : typ =
    Uint(d,m,n)

end

module Hslice = struct

  let rotate_l l x =
    let rec aux x l1 l2 =
      match x with
      | 0 -> l1 @ (List.rev l2)
      | n -> aux (n-1) (List.tl l1) ((List.hd l1) :: l2) in
    aux x l []

  let rotate_r l x =
    List.rev (rotate_l (List.rev l) x)

  let shift_l l x =
    let rec aux x acc l =
      match l with
      | [] -> acc
      | hd::tl -> match x with
                  | 0 -> aux 0 (hd::acc) tl
                  | n -> aux (n-1) ((-1)::acc) tl in
    aux x [] l

  let shift_r l x =
    List.rev (shift_l (List.rev l) x)

  (* Transforms the Shifts into Shuffles, and specialize the Const's types. *)
  let specialize_expr (env_dir:(dir,dir) Hashtbl.t)
        (env_m:(mtyp,mtyp) Hashtbl.t)
        (env_var:(ident,typ) Hashtbl.t) (e:expr) : expr =
    match e with
    | Shift(op,ExpVar v,ae) ->
       (* m  _has_ to be only one element here *)
       let m = match get_var_type env_var v with
         | Uint(_,Mint m,_) -> m
         | _ -> assert false in
       let l = gen_list_0_int m in
       (match op with
        | Lrotate -> Shuffle(v, rotate_l l (eval_arith_ne ae))
        | Rrotate -> Shuffle(v, rotate_r l (eval_arith_ne ae))
        | Lshift  -> Shuffle(v, shift_l  l (eval_arith_ne ae))
        | Rshift  -> Shuffle(v, shift_r  l (eval_arith_ne ae))
        | RAshift -> Printf.eprintf "Cannot Hslice arithmetic shifts.\n";
                     assert false)
    | Const(n,Some t) -> Const(n,Some (specialize_typ env_dir env_m t))
    | _ -> e

  let specialize_var env_var (v:var) : var = v

  let refine_types (p:p) : p = p
end


module Vslice = struct

  let get_type_m_as_int (t:typ) : int =
    match get_type_m t with
    | Mint m -> m
    | _ -> assert false

  (* Converts a shuffle into shifts/xors *)
  let specialize_shuffle (env_var:(ident,typ) Hashtbl.t)
                         (v:var) (l:int list) : expr =
    let v_typ = get_var_type env_var v in
    let size = get_type_m_as_int v_typ in

    (* Extracts the |orig|-th bit of |v| to index |dst|. *)
    let extract_bit (orig:int) (dst:int) : expr =
      if orig-dst = 0 then
        Log(And,ExpVar v,Const(1 lsl (size-1-dst),Some v_typ))
      else
        let shift_by = abs (orig - dst) in
        let shift_op = if orig-dst > 0 then Lshift else Rshift in
        Log(And,Shift(shift_op,ExpVar v,Const_e shift_by),
            Const(1 lsl (size-1-dst),Some v_typ)) in

    match l with
    | hd :: tl ->
       fold_left_i ~start:1
                   (fun (i:int) (e:expr) (n:int) -> Log(Xor,e,extract_bit n i))
                   (extract_bit hd 0) tl
    | [] -> assert false (* Shuffle pattern cannot be empty. *)

  (* Just specialize the types of Consts within this expr,
     and turn Shuffles into shift/xors. *)
  let specialize_expr (env_dir:(dir,dir) Hashtbl.t)
        (env_m:(mtyp,mtyp) Hashtbl.t)
        (env_var:(ident,typ) Hashtbl.t) (e:expr) : expr =
    match e with
    | Const(n,Some typ) -> Const(n,Some (specialize_typ env_dir env_m typ))
    | Shuffle(v,l) -> specialize_shuffle env_var v l
    | _ -> e

  let specialize_var env_var (v:var) : var = v

  let refine_types (p:p) : p = p
end

module Bslice = struct
  (* Uint(_,n,m) needs to be turned into Array(Uint(_,1,m),n) *)
  let rec refine_type (t:typ) : typ =
    match t with
    | Nat -> t
    | Uint(Bslice,Mint 1,n) -> t
    | Uint(Bslice,Mint m,1) -> Uint(Bslice,Mint 1,m)
    | Uint(Bslice,Mint m,n) -> Array(Uint(Bslice,Mint 1,m),Const_e n)
    | Array(t',n) -> Array(refine_type t',n)
    | _ -> Printf.fprintf stderr "Can't refine_type(%s).\n" (Usuba_print.typ_to_str t);
           assert false

  (* get the size in bits of a typ: a unxm has size n*m in bitslicing *)
  let rec get_typ_real_size (typ:typ) : int =
    match typ with
    | Uint(_,Mint m,n) -> m * n
    | Array(t,n) -> (get_typ_real_size t) * (eval_arith_ne n)
    | _ -> assert false (* Nat or Uint(_,Mvar _,_) *)

  (* Get the "n" associated to a type *)
  let rec get_base_n (typ:typ) : int =
    match typ with
    | Uint(_,_,n) -> n
    | Array(t,_) -> get_base_n t
    | _ -> assert false

  (*
    OUTDATED COMMENT:
    The only case in which var needs specialization is the following family:
       Example 1: `x:u8x4` will be transformed into `x:u1x32`.
                  Then, `x[2]` needs to become `x[16 .. 23]`.
       Example 2: `x:u8x1[4]` will be transformed into `x:u1x8[4]`.
                  Then, `x[2]` needs to become `x[2]` (nothing changed).
    RECENT UPDATE:
    Previously, Uint(_,n,m) were turned into Uint(_,1,n*m). This was not ideal
    as is tend to introduce unecessary ranges (as shown above), which in turn
    causes functions to take too much parameters that needed. Now that Uint
    are turned into 2d arrays, there is no need to change anything on vars
    anymore.
   *)
  let rec specialize_var env_var (v:var) : var = v

  (* Expands a const to a Tuple of 0/1 *)
  (* The tupple is padded with 0s to be of the right size (with make_0_list) *)
  let expand_const (size:int) (n:int) : expr =
    let rec make_0_list n acc =
      if n > 0 then make_0_list (n-1) (Const(0,Some (Uint(Bslice,Mint 1,1))) :: acc)
      else acc in
    let rec dec_to_binlist n =
      if n > 0 then
        (Const (n mod 2,Some (Uint(Bslice,Mint 1,1))))::(dec_to_binlist (n/2))
      else [] in
    let l = dec_to_binlist n in
    let len = List.length l in
    let diff = size - len in
    Tuple((make_0_list diff []) @ (List.rev l))

  (* Constants need to be turned into tuples of booleans (boolean = 0/1) *)
  let specialize_const (n:int) (typ:typ) : expr =
    let size = get_typ_real_size typ in
    (* The special case for size = 1 avoids to needlessly create a Tuple *)
    if size = 1 then Const(n, Some typ)
    else expand_const size n

  let rec specialize_expr (env_dir:(dir,dir) Hashtbl.t)
            (env_m:(mtyp,mtyp) Hashtbl.t)
            (env_var:(ident,typ) Hashtbl.t) (e:expr) : expr =
    match e with
    | Const(n,Some typ) ->
       (* It's safe to specialize |typ| here because after
          specialization, it will still have the same size.

          Moreover, it might be _needed_ to specialize |typ| first,
          because if it's word-size m is polymorphic, then it needs to
          be specialized to know the actual size of the const. (I
          don't have any example with polymorphic word-size
          though... But I expect my future self to thank me for
          specializing |typ| here) *)
       let typ = refine_type (specialize_typ env_dir env_m typ) in
       specialize_const n typ
    | ExpVar v -> ExpVar (specialize_var env_var v)
    | Not (ExpVar v) -> Not (ExpVar(specialize_var env_var v))
    | Shift(op,ExpVar x, ae) ->
       Shift(op,ExpVar(specialize_var env_var x),ae)
    | Log(op,ExpVar x, ExpVar y) ->
       Log(op,ExpVar(specialize_var env_var x),ExpVar(specialize_var env_var y))
    | Log(op,ExpVar x, y) ->
       Log(op,ExpVar(specialize_var env_var x),y)
    | Log(op,x, ExpVar y) ->
       Log(op,x,ExpVar(specialize_var env_var y))
    | Log(op,x,y) ->
       Log(op,x,y)
    | Shuffle(v,l) -> Shuffle(specialize_var env_var v,l)
    | Arith(op,ExpVar x,ExpVar y) ->
       Arith(op,ExpVar(specialize_var env_var x),ExpVar(specialize_var env_var y))
    | _ -> Printf.eprintf "Monomorphize::Bslice::specialize_expr: Invalid expr: %s\n"
             (Usuba_print.expr_to_str e);
           assert false

  let specialize_vars env_var (vs:var list) : var list =
    List.map (specialize_var env_var) vs

  let loop_log_it = fresh_ident "_log_it"

  let apply_loop_it (v:var) : var =
    Index(v,Var_e loop_log_it)

  let specialize_eqn (env_dir:(dir,dir) Hashtbl.t)
                     (env_m:(mtyp,mtyp) Hashtbl.t)
                     (env_var:(ident,typ) Hashtbl.t)
                     (orig:(ident*deq_i) list) (vs:var list) (e:expr) : deq =
    let vs = specialize_vars env_var vs in
    let e  = specialize_expr env_dir env_m env_var e in
    match e with
    | ExpVar v ->
       (match get_var_m env_var v with
        | Mint m when !compact && m > 1 ->
           (* We have a ^/&/| between two arrays -> generate a loop *)
           { orig=orig;
             content=Loop(loop_log_it,Const_e 0,Op_e (Sub,Const_e m,Const_e 1),
                          [ {orig=orig;
                             content=Eqn(List.map apply_loop_it vs,
                                         ExpVar (apply_loop_it v), false)} ], [])}
        | _ -> (* Not between two arrays -> leave it as a simple equation *)
           { orig=orig; content=Eqn(vs,e,false) })
    | Log(op,ExpVar x,ExpVar y) ->
       (match get_var_m env_var x with
        | Mint m when !compact && m > 1 ->
           (* We have a ^/&/| between two arrays -> generate a loop *)
           { orig=orig;
             content=Loop(loop_log_it,Const_e 0,Op_e (Sub,Const_e m,Const_e 1),
                          [ {orig=orig;
                             content=Eqn(List.map apply_loop_it vs,
                                         Log(op,ExpVar (apply_loop_it x),
                                             ExpVar (apply_loop_it y)), false)} ], [])}
        | _ -> (* Not between two arrays -> leave it as a simple equation *)
           {orig=orig;content=Eqn(vs,e,false)})
    | Not (ExpVar v) ->
       (match get_var_m env_var v with
        | Mint m when !compact && m > 1 ->
           (* We have a ^/&/| between two arrays -> generate a loop *)
           { orig=orig;
             content=Loop(loop_log_it,Const_e 0,Op_e (Sub,Const_e m,Const_e 1),
                [ {orig=orig;
                   content=Eqn(List.map apply_loop_it vs,
                               Not (ExpVar (apply_loop_it v)), false)} ], [])}
        | _ -> (* Not between two arrays -> leave it as a simple equation *)
           {orig=orig; content=Eqn(vs,e,false)})
    | _ -> {orig=orig; content=Eqn(vs,e,false)}



  let refine_types (p:p) : p =
    List.map (fun vd -> { vd with vd_typ = refine_type vd.vd_typ }) p
end


(* Generates a function name based on its polymorphic name and its monomorphization *)
let gen_fun_name (f:ident) (ldir:dir list) (lmtyp:mtyp list): ident =
  fresh_ident
    (f.name ^
       (join "_" (List.map (function
                             | Hslice -> "H"
                             | Vslice -> "V"
                             | Bslice -> "B"
                             | Natdir -> "Nat"
                             | _ -> assert false) ldir)) ^
         (join "_" (List.map (function
                               | Mint n -> string_of_int n
                               | Mnat   -> "nat"
                               | _ -> assert false) lmtyp)))

(* Mainly useful for bitslicing to convert Uint(_,m,_) to Array(Uint(_,1,_),m) *)
let refine_types (p:p) : p =
  match p with
  | [] -> []
  | hd::_ ->  match get_type_dir hd.vd_typ with
              | Bslice -> Bslice.refine_types p
              | Hslice -> Hslice.refine_types p
              | Vslice -> Vslice.refine_types p
              | Natdir -> p
              | _ -> assert false

let specialize_p (env_dir:(dir,dir) Hashtbl.t)
                 (env_m:(mtyp,mtyp) Hashtbl.t)
                 (p:p) : p =
  List.map (fun v -> { v with vd_typ = specialize_typ env_dir env_m v.vd_typ }) p

let specialize_var (env_var:(ident, typ) Hashtbl.t) (v:var) : var =
  match get_var_dir env_var v with
  | Bslice -> Bslice.specialize_var env_var v
  | Hslice -> Hslice.specialize_var env_var v
  | Vslice -> Vslice.specialize_var env_var v
  | Natdir -> v
  | _ -> assert false

(* Called on the parameters of a function call -> those should be ExpVars only *)
let specialize_expr_var (env_var:(ident, typ) Hashtbl.t) (e:expr) : expr =
  match e with
  | ExpVar v -> ExpVar (specialize_var env_var v)
  | _ -> assert false

(* Given a list of var_d (p), and a list of types, update the dir/m of each
     var_d according to the corresponding type in the list of types *)
let match_types env_dir env_m (p:p) (typs:typ list) : p =
  (* updates the dir in tdest with the dir in tdir *)
  let rec update_dir_m (t_dest:typ) (t_dir_m:typ) : typ =
    match t_dest with
    | Nat -> t_dest
    | Uint(_,_,n) -> Uint(get_type_dir t_dir_m,get_type_m t_dir_m,n)
    | Array(t,s)  -> Array(update_dir_m t t_dir_m,s) in
  List.map2 (fun vd t ->
             Hashtbl.replace env_dir (get_type_dir vd.vd_typ) (get_type_dir t);
             Hashtbl.replace env_m (get_type_m vd.vd_typ) (get_type_m t);
             { vd with vd_typ = update_dir_m vd.vd_typ t }
            ) p typs

let rec specialize_fun_call
          (all_nodes:(ident,def) Hashtbl.t)
          (specialized_nodes:(ident,(ident*(dir list)*(mtyp list),def) Hashtbl.t) Hashtbl.t)
          (env_var:(ident, typ) Hashtbl.t)
          (orig:(ident*deq_i) list) (vs:var list) (f:ident)
          (l:expr list) (sync:bool) : deq =
  let env_dir = Hashtbl.create 10 in
  let env_m   = Hashtbl.create 10 in

  let typs_out = List.map (get_var_type env_var) vs in
  let typs_in  = flat_map (get_expr_type (Hashtbl.create 1) env_var) l in

  let def   = Hashtbl.find all_nodes f in
  let p_in  = match_types env_dir env_m def.p_in  typs_in  in
  let p_out = match_types env_dir env_m def.p_out typs_out in

  let ldir  = List.sort compare (values env_dir) in
  let lmtyp = List.sort compare (values env_m) in
  let f'   = gen_fun_name f ldir lmtyp in

  replace_key_2nd_layer specialized_nodes f (f',ldir,lmtyp)
                        { def with
                          id    = f';
                          p_in  = refine_types p_in;
                          p_out = refine_types p_out;
                          node  = match def.node with
                                  | Single(vars,body) ->
                                     specialize_node all_nodes specialized_nodes
                                                     env_dir env_m p_in p_out vars body
                                  | _ -> def.node };

  let vs = List.map (specialize_var env_var) vs in
  let l  = List.map (specialize_expr_var env_var) l in

  { orig=orig; content=Eqn(vs,Fun(f',l),sync) }


(* Note that expressions have been normalized, and are therefore not reccursive
     at this point. *)
and specialize_expr (all_nodes:(ident,def) Hashtbl.t)
                    (specialized_nodes:(ident,(ident*(dir list)*(mtyp list),def) Hashtbl.t) Hashtbl.t)
                    (env_dir:(dir,dir) Hashtbl.t)
                    (env_m:(mtyp,mtyp) Hashtbl.t)
                    (env_var:(ident, typ) Hashtbl.t)
                    (orig:(ident*deq_i) list) (vs:var list) (e:expr) (sync:bool)
    : deq =
  match e with
  (* When a function call happens, we need to specialize the function called *)
  | Fun(f,l) -> if f.name = "refresh" then { orig=orig; content=Eqn(vs,e,sync) }
                else specialize_fun_call all_nodes specialized_nodes
                                         env_var orig vs f l sync
  (* Otherwise (not a function call), we delegate to the modules of each Slicing *)
  | _ -> match get_var_dir env_var (List.hd vs) with
         | Hslice ->
            { orig=orig; content=Eqn(vs, Hslice.specialize_expr env_dir env_m env_var e, sync) }
         | Vslice ->
            { orig=orig; content=Eqn(vs, Vslice.specialize_expr env_dir env_m env_var e, sync) }
         | Bslice -> Bslice.specialize_eqn env_dir env_m env_var orig vs e;
                     (* Eqn(Bslice.specialize_vars env_var vs, *)
                     (*     Bslice.specialize_expr env_dir env_m env_var e, *)
                     (*     sync) *)
         | Natdir -> { orig=orig; content=Eqn(vs,e,sync) } (* A Nat, doing nothing *)
         | _ -> assert false


and specialize_deqs (all_nodes:(ident,def) Hashtbl.t)
                    (specialized_nodes:(ident,(ident*(dir list)*(mtyp list),def) Hashtbl.t) Hashtbl.t)
                    (env_dir:(dir,dir) Hashtbl.t)
                    (env_m:(mtyp,mtyp) Hashtbl.t)
                    (env_var:(ident, typ) Hashtbl.t) (deqs:deq list) : deq list =
  List.map (fun d ->
            match d.content with
            | Eqn(vs,e,sync) -> specialize_expr all_nodes specialized_nodes
                                                env_dir env_m env_var d.orig vs e sync
            | Loop(e,ei,ef,l,opts) ->
               Hashtbl.add env_var e Nat;
               let x' = Loop(e,ei,ef,specialize_deqs all_nodes specialized_nodes
                                                     env_dir env_m env_var l,opts) in
               Hashtbl.remove env_var e;
               { d with content = x' })
           deqs

(* Called by either specialize_entry of specialize_fun_call.
     Looked at either of those functions for more details *)
and specialize_node (all_nodes:(ident,def) Hashtbl.t)
                    (specialized_nodes:(ident,(ident*(dir list)*(mtyp list),def) Hashtbl.t) Hashtbl.t)
                    (env_dir:(dir,dir) Hashtbl.t)
                    (env_m:(mtyp,mtyp) Hashtbl.t)
                    (p_in:p) (p_out:p) (vars:p) (body:deq list): def_i =
  let vars = specialize_p env_dir env_m vars  in
  let env_var = build_env_var p_in p_out vars in

  let body = specialize_deqs all_nodes specialized_nodes env_dir env_m env_var body in

  Single(refine_types vars, body)


(* We call "entry" a node which is called by not other.
     Their monomorphization is a bit special: the specialization of the parameters
     depends on the compilation flags rather than how it's called (since there is
     no way to know how it will be called) *)
let specialize_entry (all_nodes:(ident,def) Hashtbl.t)
                     (specialized_nodes:(ident,(ident*(dir list)*(mtyp list),def) Hashtbl.t) Hashtbl.t)
                     (env_dir:(dir,dir) Hashtbl.t) (def:def) (conf:config) : unit =

  let p_in  = specialize_p env_dir (Hashtbl.create 1) def.p_in  in
  let p_out = specialize_p env_dir (Hashtbl.create 1) def.p_out in

  replace_key_2nd_layer specialized_nodes def.id (def.id,[],[])
                        { def with
                          p_in  = refine_types p_in;
                          p_out = refine_types p_out;
                          node  = match def.node with
                                  | Single(vars,body) ->
                                     specialize_node all_nodes specialized_nodes
                                                     env_dir (Hashtbl.create 1) p_in p_out vars body
                                  | _ -> def.node }


let monomorphize (prog:prog) (conf:config) : prog =
  compact := conf.compact;

  (* Getting the default dir (command line parameter) *)
  let spec_dir = match conf.slicing_set with
    | false -> Vslice (* not used *)
    | true  -> match conf.slicing_type with
               | V -> Vslice
               | H -> Hslice
               | B -> Bslice in
  let env_dir = Hashtbl.create 10 in
  Hashtbl.add env_dir default_dir spec_dir;

  (* Environment of all (non-monomorphized) nodes *)
  let all_nodes = Hashtbl.create 10 in
  List.iter (fun f -> Hashtbl.add all_nodes f.id f) prog.nodes;

  (* Environment of monomorphized nodes *)
  let specialized_nodes = Hashtbl.create 100 in

  (* Starting monomorphization from the main *)
  specialize_entry all_nodes specialized_nodes env_dir (last prog.nodes) conf;

  (* Monomorphizing the nodes that aren't called by the main *)
  List.iter (fun def -> match Hashtbl.find_opt specialized_nodes def.id with
                        | Some _ -> ()
                        | None   -> specialize_entry all_nodes specialized_nodes
                                                     env_dir def conf)
            prog.nodes;

  (* Reconstructing the program from the monomorphized nodes *)
  { nodes =
      flat_map
        (fun def ->
         let monos_hash = Hashtbl.find specialized_nodes def.id in
         values monos_hash) prog.nodes }
