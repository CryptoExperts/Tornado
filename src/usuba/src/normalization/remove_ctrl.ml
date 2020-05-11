(***************************************************************************** )
                              remove_ctrl.ml

  Removes 'When' and 'Merge' by using masks instead.

( *************************************************************************** *)



open Usuba_AST
open Basic_utils
open Utils

let rec clean_expr (e:expr) : expr =
  match e with
  | Const _ | ExpVar _ | Shuffle _ -> e
  | Tuple l -> Tuple(List.map clean_expr l)
  | Not e   -> Not (clean_expr e)
  | Shift(op,e,ae)  -> Shift(op,clean_expr e,ae)
  | Log(op,e1,e2)   -> Log(op,e1,e2)
  | Arith(op,e1,e2) -> Arith(op,e1,e2)
  | Fun(f,l)        -> Fun(f,List.map clean_expr l)
  (* Removing When and Merge *)
  | When(e,_,_)     -> e
  | Merge(id,l)     ->
     Printf.eprintf "Removing Merge: injecting untyped const might end up poorly...\n";
     List.fold_left
                         (fun x y -> Log(Or,x,y))
                         (Const(0,None))
                         (List.map (fun (c,e) ->
                                    match c with
                                    | True  -> Log(And,(clean_expr e), ExpVar(Var id))
                                    | False -> Log(And,(clean_expr e), Not (ExpVar(Var id)))) l)

  | _ -> assert false

let rec clean_deq (deq:deq) : deq =
  { deq with content =
  match deq.content with
  | Eqn(lhs,e,sync) -> Eqn(lhs,clean_expr e,sync)
  | Loop(x,ei,ef,dl,opts) -> Loop(x,ei,ef,List.map clean_deq dl,opts) }

let clean_def (def:def) : def =
  match def.node with
  | Single(vars,body) -> {def with node = Single(vars,List.map clean_deq body) }
  | _ -> def

let remove_ctrl (prog:prog) (conf:config) : prog =
  { nodes = List.map clean_def prog.nodes }
