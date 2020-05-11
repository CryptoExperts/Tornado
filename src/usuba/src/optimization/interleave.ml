open Usuba_AST
open Basic_utils
open Utils


module Dup3 = struct

  let dup_id id = { id with name = id.name ^ "__2" }
  let dup3_id id = { id with name = id.name ^ "__3" }

  let rec dup3_var (v:var) : var =
    match v with
    | Var id -> Var (dup3_id id)
    | Index(v,i) -> Index(dup3_var v,i)
    | _ -> assert false

  let rec dup3_expr (e:expr) : expr =
    match e with
    | Const _ -> e
    | ExpVar v -> ExpVar(dup3_var v)
    | Tuple l -> Tuple(List.map dup3_expr l)
    | Shift(op,e,ae) -> Shift(op,dup3_expr e,ae)
    | Log(op,x,y)    -> Log(op,dup3_expr x,dup3_expr y)
    | Not e    -> Not (dup3_expr e)
    | Shuffle(v,p)   -> Shuffle(dup3_var v,p)
    | Arith(op,x,y)  -> Arith(op,dup3_expr x,dup3_expr y)
    | Fun(f,l)       -> Fun(f,List.map dup3_expr l)
    | _ -> assert false

  let rec dup_var (v:var) : var =
    match v with
    | Var id -> Var (dup_id id)
    | Index(v,i) -> Index(dup_var v,i)
    | _ -> assert false

  let rec dup_expr (e:expr) : expr =
    match e with
    | Const _ -> e
    | ExpVar v -> ExpVar(dup_var v)
    | Tuple l -> Tuple(List.map dup_expr l)
    | Shift(op,e,ae) -> Shift(op,dup_expr e,ae)
    | Not e    -> Not (dup_expr e)
    | Log(op,x,y)    -> Log(op,dup_expr x,dup_expr y)
    | Shuffle(v,p)   -> Shuffle(dup_var v,p)
    | Arith(op,x,y)  -> Arith(op,dup_expr x,dup_expr y)
    | Fun(f,l)       -> Fun(f,List.map dup_expr l)
    | _ -> assert false

  let rec interleave_deqs (deqs:deq list) : deq list =
    flat_map (fun d ->
              match d.content with
              | Eqn(lhs,e,sync) ->
                 [ d ; { orig=d.orig;
                         content=Eqn(List.map dup_var lhs,dup_expr e,sync)};
                   { orig=d.orig;
                     content=Eqn(List.map dup3_var lhs,dup3_expr e,sync)} ]
              | Loop(i,ei,ef,l,opts) ->
                 [ { d with content=Loop(i,ei,ef,interleave_deqs l,opts) } ]) deqs

  let dup_p (p:p) : p =
    flat_map (fun vd -> [ vd;
                          { vd with vd_id = dup_id vd.vd_id };
                          { vd with vd_id = dup3_id vd.vd_id } ]) p

  let interleave_def (def:def) : def =
    match def.node with
    | Single(vars,body) ->
       { def with p_in  = dup_p def.p_in;
                  p_out = dup_p def.p_out;
                  node  = Single(dup_p vars,interleave_deqs body) }
    | _ -> assert false

  let interleave (prog:prog) (conf:config) : prog =
    { nodes = apply_last prog.nodes interleave_def }

end



(* GP-64: 37.05 -> 27.35  cycles/byte
   SSE  : 16.35 -> 14.70  cycles/byte
   AVX  : 13.40 -> 10.43  cycles/byte
   AVX2 : 7.70  -> 6.00   cycles/byte
*)
module Dup2 = struct

  let dup_id id = { id with name = id.name ^ "__2" }

  let rec dup_var (v:var) : var =
    match v with
    | Var id -> Var (dup_id id)
    | Index(v,i) -> Index(dup_var v,i)
    | _ -> assert false

  let rec dup_expr (e:expr) : expr =
    match e with
    | Const _ -> e
    | ExpVar v -> ExpVar(dup_var v)
    | Tuple l -> Tuple(List.map dup_expr l)
    | Shift(op,e,ae) -> Shift(op,dup_expr e,ae)
    | Log(op,x,y)    -> Log(op,dup_expr x,dup_expr y)
    | Not e    -> Not (dup_expr e)
    | Shuffle(v,p)   -> Shuffle(dup_var v,p)
    | Arith(op,x,y)  -> Arith(op,dup_expr x,dup_expr y)
    | Fun(f,l)       -> Fun(f,List.map dup_expr l)
    | _ -> assert false

  let rec interleave_deqs (deqs:deq list) : deq list =
    flat_map (fun d ->
              match d.content with
              | Eqn(lhs,e,sync) ->
                 [ d ;
                   { orig=d.orig;
                     content=Eqn(List.map dup_var lhs,dup_expr e,sync)} ]
              | Loop(i,ei,ef,l,opts) ->
                 [ {orig=d.orig;
                    content=Loop(i,ei,ef,interleave_deqs l,opts)} ]) deqs

  let dup_p (p:p) : p =
    flat_map (fun vd -> [ vd; { vd with vd_id = dup_id vd.vd_id } ] ) p

  let interleave_def (def:def) : def =
    match def.node with
    | Single(vars,body) ->
       { def with p_in  = dup_p def.p_in;
                  p_out = dup_p def.p_out;
                  node  = Single(dup_p vars,interleave_deqs body) }
    | _ -> assert false

  let interleave (prog:prog) (conf:config) : prog =
    { nodes = apply_last prog.nodes interleave_def }

end



(* GP-64: 37.05 -> 28.65  cycles/byte
   SSE  : 16.35 -> 13.83  cycles/byte
   AVX  : 13.40 -> 10.30  cycles/byte
   AVX2 : 7.70  -> 5.95   cycles/byte
*)
module Dup2_nofunc = struct

  let make_2nd_id id = { id with name = id.name ^ "__2" }

  let rec make_2nd_var (v:var) : var =
    match v with
    | Var id -> Var (make_2nd_id id)
    | Index(v,i) -> Index(make_2nd_var v,i)
    | _ -> assert false

  let rec make_2nd_expr (e:expr) : expr =
    match e with
    | Const _ -> e
    | ExpVar v -> ExpVar(make_2nd_var v)
    | Tuple l -> Tuple(List.map make_2nd_expr l)
    | Shift(op,e,ae) -> Shift(op,make_2nd_expr e,ae)
    | Log(op,x,y)    -> Log(op,make_2nd_expr x,make_2nd_expr y)
    | Not e    -> Not (make_2nd_expr e)
    | Shuffle(v,p)   -> Shuffle(make_2nd_var v,p)
    | Arith(op,x,y)  -> Arith(op,make_2nd_expr x,make_2nd_expr y)
    | Fun(f,l)       -> Fun(f,List.map make_2nd_expr l)
    | _ -> Printf.printf "Not valid: %s\n" (Usuba_print.expr_to_str e);
           assert false

  let rec dup_var (v:var) : var list =
    [ v ; make_2nd_var v ]

  let rec dup_expr (e:expr) : expr list =
    [ e ; make_2nd_expr e ]

  let rec interleave_deqs (deqs:deq list) : deq list =
    flat_map (fun d ->
              match d.content with
              | Eqn(lhs,e,sync) ->
                 begin match e with
                       | Fun(f,l) ->
                          [ {d with content=Eqn(flat_map dup_var lhs,
                                               Fun(f,flat_map dup_expr l), sync)} ]
                       | _ -> [ d ;
                                { d with content=Eqn(List.map make_2nd_var lhs,
                                                     make_2nd_expr e,sync)} ]
                 end
              | Loop(i,ei,ef,l,opts) ->
                 [ { d with content=Loop(i,ei,ef,interleave_deqs l,opts) } ]) deqs

  let dup_p (p:p) : p =
    flat_map (fun vd -> [ vd; { vd with vd_id = make_2nd_id vd.vd_id } ]) p

  let interleave_def (def:def) : def =
    match def.node with
    | Single(vars,body) ->
       { def with p_in  = dup_p def.p_in;
                  p_out = dup_p def.p_out;
                  node  = Single(dup_p vars,interleave_deqs body) }
    | _ -> assert false

  let interleave (prog:prog) (conf:config) : prog =
    { nodes = List.map interleave_def prog.nodes }

end


(* GP-64: 37.05 ->    cycles/byte
   SSE  : 16.35 ->    cycles/byte
   AVX  : 13.40 ->    cycles/byte
   AVX2 : 7.70  ->    cycles/byte
*)
module Dup2_nofunc_param = struct

  (*
  let rec map_n (n:int) (f:'a -> 'b) (l:'a list) (acc:'b list) (res:'b list): 'b list =
    match l with
    | [] -> List.rev (acc @ res)
    | hd::tl -> if List.length acc = n then
                  map_n n f tl [f hd] (hd :: (acc @ res))
                else
                  map_n n f tl ((f hd) :: acc) (hd :: res)
  (* Warning: shadowing (and using) map_n above *)
  let map_n (n:int) (f:'a -> 'b) (l:'a list) : 'b list =
    map_n n f l [] []
   *)

  let build_complete_env_var (p_in:p) (p_out:p) (vars:p) : (var, var_d) Hashtbl.t =
    let env = Hashtbl.create 100 in

    let add_to_env (vd:var_d) : unit =
      Hashtbl.add env (Var vd.vd_id) vd in

    List.iter add_to_env p_in;
    List.iter add_to_env p_out;
    List.iter add_to_env vars;

    env

  let make_2nd_id id = { id with name = id.name ^ "__2" }

  let rec make_2nd_var env_var (v:var) : var =
    match v with
    | Var id -> ( match List.mem Pconst (Hashtbl.find env_var (get_var_base v)).vd_opts with
                  | false -> Var (make_2nd_id id)
                  | true -> v )
    | Index(v,i) -> Index(make_2nd_var env_var v,i)
    | _ -> assert false

  let rec make_2nd_expr env_var (e:expr) : expr =
    match e with
    | Const _ -> e
    | ExpVar v -> ExpVar(make_2nd_var env_var v)
    | Tuple l -> Tuple(List.map (make_2nd_expr env_var) l)
    | Shift(op,e,ae) -> Shift(op,make_2nd_expr env_var e,ae)
    | Log(op,x,y)    -> Log(op,make_2nd_expr env_var x,make_2nd_expr env_var y)
    | Not e    -> Not (make_2nd_expr env_var e)
    | Shuffle(v,p)   -> Shuffle(make_2nd_var env_var v,p)
    | Arith(op,x,y)  -> Arith(op,make_2nd_expr env_var x,make_2nd_expr env_var y)
    | Fun(f,l)       -> Fun(f,List.map (make_2nd_expr env_var) l)
    | _ -> Printf.printf "Not valid: %s\n" (Usuba_print.expr_to_str e);
           assert false

  let rec dup_var env_var (v:var) : var list =
    match List.mem Pconst (Hashtbl.find env_var (get_var_base v)).vd_opts with
    | false -> [ v ; make_2nd_var env_var v ]
    | true -> [ v ]

  (* TODO: this feels very wrong *)
  let rec dup_expr env_var (e:expr) : expr list =
    match e with
    | ExpVar v -> List.map (fun v -> ExpVar v) (dup_var env_var v)
    | _ -> [ e ; make_2nd_expr env_var e ]

  (*let rec map_n (n:int) (f:'a -> ('b option * 'b option)) (l:'a list)
                (acc:'b list) (res:'b list) : 'b list =*)
  let rec map_n (n:int) f l acc res =
    match l with
    | [] -> List.rev (acc @ res)
    | hd::tl ->
       let res = if List.length acc = n then acc @ res else res in
       let acc = if List.length acc = n then [] else acc in
       let hd, hd' = f hd in
                match hd, hd' with
                | None, None -> map_n n f tl [ ] (acc @ res)
                | None, Some hd' -> map_n n f tl [] (hd' :: (acc @ res))
                | Some hd, Some hd' -> map_n n f tl (hd' :: acc) (hd :: res)
                | Some hd, None -> map_n n f tl acc (hd :: res)
  (* Warning: shadowing (and using) map_n above *)
  let map_n (n:int) (f:'a -> ('b option * 'b option)) (l:'a list) : 'b list =
    map_n n f l [] []
  let rec interleave_deqs env_var (g:int) (deqs:deq list) : deq list =
    map_n g (fun d ->
             match d.content with
             | Eqn(lhs,e,sync) ->
                begin match e with
                      | Fun(f,l) ->
                         ( None,
                           Some ({d with
                                   content=Eqn(flat_map (dup_var env_var) lhs,
                                               Fun(f,flat_map (dup_expr env_var) l), sync)}))
                      | _ -> ( Some d,
                               Some({d with
                                      content=Eqn(List.map (make_2nd_var env_var) lhs,
                                                  make_2nd_expr env_var e, sync)}) )
                end
             | Loop(i,ei,ef,l,opts) ->
                ( None,
                  Some ({d with content=Loop(i,ei,ef,interleave_deqs env_var g l,opts)}))) deqs

  let dup_p (p:p) : p =
    flat_map (fun vd -> match List.mem Pconst vd.vd_opts with
                        | true  -> [ vd ]
                        | false -> [ vd; { vd with vd_id = make_2nd_id vd.vd_id } ]) p

  let interleave_def (g:int) (def:def) : def =
    match def.node with
    | Single(vars,body) ->
       let p_in  = dup_p def.p_in in
       let p_out = dup_p def.p_out in
       let vars  = dup_p vars in
       let env_var = build_complete_env_var p_in p_out vars in
       { def with p_in  = p_in;
                  p_out = p_out;
                  node  = Single(vars,interleave_deqs env_var g body) }
    | _ -> assert false

  let interleave (g:int) (prog:prog) (conf:config) : prog =
    { nodes = List.map (interleave_def g) prog.nodes }

end



let interleave (prog:prog) (conf:config) =
  Dup2_nofunc_param.interleave conf.interleave prog conf
 (*Dup2.interleave prog conf*)
