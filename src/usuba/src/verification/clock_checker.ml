open Usuba_AST
open Basic_utils
open Utils


(* TODO
  - debug this!
  - elements of a tuple should be able to have different clocks
*)

(* Combine clocks. Defclock is the only interesting case:
  x && Defclock = x, for all x          (commutative)      *)
let and_ck (x:clock) (y:clock) : clock * bool =
  match x with
  | Defclock -> y, true
  | _ -> match y with
         | Defclock -> x, true
         | _ -> x, y = x

let init_env (p_in:p) (p_out:p) (vars:p) =
  let env = Hashtbl.create 100 in
  List.iter (fun vd -> Hashtbl.add env vd.vd_id vd.vd_ck) p_in;
  List.iter (fun vd -> Hashtbl.add env vd.vd_id vd.vd_ck) p_out;
  List.iter (fun vd -> Hashtbl.add env vd.vd_id vd.vd_ck) vars;
  env

let rec get_clock env (v: var) : clock =
  match v with
  | Var id -> (try Hashtbl.find env id with
                 Not_found -> Printf.fprintf stderr "Not found: %s\n" id.name;
                              raise Not_found)
  | Index(v,_)
  | Range(v,_,_) | Slice(v,_)-> get_clock env v

let rec clock_expr env (e:expr) : clock * bool =
  match e with
  | Const _ -> Defclock, true
  | ExpVar v -> get_clock env v, true
  | Shuffle(v,_) -> get_clock env v, true
  | Tuple l | Fun(_,l) | Fun_v(_,_,l)
        -> let l = List.map (clock_expr env) l in
           List.fold_left (fun (ck1,ok1) (ck2,ok2)
                           -> let (ck,ok) = and_ck ck1 ck2 in
                              (ck,ok1 && ok2 && ok)) (List.nth l 0) l
  | Not e -> clock_expr env e
  | Shift(_,e,_) -> clock_expr env e
  | Log(_,e1,e2) | Arith(_,e1,e2) | Fby(e1,e2,_)
                   -> let (ck1,ok1) = clock_expr env e1 in
                      let (ck2,ok2) = clock_expr env e2 in
                      let (ck,ok) = and_ck ck1 ck2 in
                      (ck, ok1 && ok2 && ok)
  | When(e,cstr,id) -> let (ck1,ok1) = clock_expr env e in
                       let ck2 = get_clock env (Var id) in
                       let (ck,ok) = and_ck ck1 ck2 in
                       (match cstr with
                        | True  -> On(ck,id), ok && ok1
                        | False -> Onot(ck,id), ok && ok1)
  | Merge(x,l) -> let ck = get_clock env (Var x) in
                  let l' = List.map (fun (cstr,e) ->
                                     let (ck1,ok1) = clock_expr env e in
                                     match cstr with
                                     | True -> (match ck1 with
                                                | On(c,x')  -> ok1 && x' = x
                                                | Defclock -> ok1
                                                | _ -> false)
                                     | False -> (match ck1 with
                                                 | Onot(c,x') -> ok1 && x' = x
                                                 | Defclock  -> ok1
                                                 | _ -> false)) l in
                  ck, List.fold_left (&&) true l'

let rec check_deq env (deq:deq) : bool =
  match deq.content with
  | Eqn(lhs,e,_) -> let l = List.map (get_clock env) lhs in
                    let (ck,is_ok) = clock_expr env e in
                    is_ok && List.for_all (fun x -> x = ck) l
  | Loop(_,_,_,l,_) -> List.for_all (check_deq env) l

let check_def (def:def) : bool =
  match def.node with
  | Single(vars,body) -> let env = init_env def.p_in def.p_out vars in
                         List.for_all (check_deq env) body
  | Multiple l -> List.fold_left (&&) true
                                 (List.map (fun x ->
                                            match x with
                                            | Single(vars,body) ->
                                               let env = init_env def.p_in def.p_out vars in
                                               List.for_all (check_deq env) body
                                            | _ -> true) l)
  | _ -> true

let check_prog (prog:prog) : bool =
  List.for_all check_def prog.nodes

let is_clocked = check_prog
