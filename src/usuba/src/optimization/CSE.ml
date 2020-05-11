(******************************************************************* )
                                  CSE.ml

   Common Subexpression Elimination (CSE) is yet another very common
   optimization that consists in replacing common expressions by
   variables containing their values.
   Typically,

      x = a ^ b
      y = a ^ b

   Is replaced by

      x = a ^ b
      y = x

   (and then, y can probably be removed altogether and x be used
   instead. This is done by the module Copy_propagation)


   Nothing too fancy is going one here: we go through each expression
   of the program while maintaining a hash table { expr : variable list }
   that contains every expression already available, and the variables
   that contains its result. Note the "variable list" and not
   "variable": this is because of function calls, that can compute
   several values. Note that removing function calls is only valid
   because functions are pure and stateless.


   We need to be a bit careful with loops. For instance, consider:

     forall i in [1, 3] { x[i] = y[i] ^ z[i] }
     forall i in [4, 6] { x[i] = y[i] ^ z[i] }

   It would be wrong for this module to replace the second loop's body
   with `x[i] = x[i]` (even though the previous loop was already
   computing `y[i] ^ z[i]` and putting the result in `x[i]`...).
   This is handled by passing a copy of the expression environment to
   the reccursive calls that performs CSE inside loops body.
   Note that this can result in some CSE not being performed because
   Usuba doesn't do loop-invariant code motion yet. This shouldn't
   matter too much for now though.
   TODO: add a loop-invariant code motion pass.


( ***************************************************************** *)

open Usuba_AST
open Basic_utils
open Utils

let rec cse_expr (env_expr:(expr,var list) Hashtbl.t) (e:expr) : expr =
  match Hashtbl.find_opt env_expr e with
  | Some vl ->
     (* Already computed *)
     (match vl with
      | v :: [] -> ExpVar v
      | l -> Tuple (List.map (fun v -> ExpVar v) l))
  | None ->
     (* Not yet computed; looking if its subexpressions are already
        computed. (ie, reccursive calls through |e|) *)
     match e with
     | Const _   -> e
     | ExpVar _  -> e
     | Shuffle _ -> e
     | Tuple l   -> Tuple (List.map (cse_expr env_expr) l)
     | Not e'    -> Not (cse_expr env_expr e')
     | Shift(op,e',ae) -> Shift(op,cse_expr env_expr e',ae)
     | Log(op,x,y)     -> Log(op,cse_expr env_expr x,cse_expr env_expr y)
     | Arith(op,x,y)   -> Arith(op,cse_expr env_expr x,cse_expr env_expr y)
     | Fun(f,l)        -> Fun(f,List.map (cse_expr env_expr) l)
     | _ -> Printf.eprintf "cse_expr: invalid expr: %s.\n"
              (Usuba_print.expr_to_str e);
            assert false

let rec cse_deqs (env_expr:(expr,var list) Hashtbl.t) (deqs:deq list)
        : deq list =
  List.map (fun d -> match d.content with
      | Eqn(lhs,e,sync) ->
         let e' = cse_expr env_expr e in
         (* Only adding |e'| to |env_expr| if it's not already in it,
            just to have all subsequent use of the same variable:
                x = a ^ b;
                y = a ^ b;
                z = a ^ b;
             becomes:
                x = a ^ b;
                y = x;
                z = x;
             instead of:
                x = a ^ b;
                y = x;
                z = y;
          *)
         (match Hashtbl.find_opt env_expr e' with
          | Some _ -> ()
          | None -> match e' with
                    | Const _ -> () (* Don't replace Consts by variables *)
                    | _-> Hashtbl.add env_expr e' lhs);
         { d with content = Eqn(lhs,e',sync) }
      | Loop(i,ei,ef,dl,opts) ->
         (* Passing a copy of |env_expr| to the loop, so that nothing
            from the loop's body leaks outside. *)
         let env_expr_copy = Hashtbl.copy env_expr in
         { d with content = Loop(i,ei,ef,cse_deqs env_expr_copy dl,opts) }) deqs

let cse_def (def:def) : def =
  match def.node with
  | Single(vars,body) ->
     (* |env_expr|: the environment of expressions already
        computed. *)
     let env_expr : (expr,var list) Hashtbl.t = Hashtbl.create 100 in
     { def with node = Single(vars,cse_deqs env_expr body) }
  | _ -> def

let cse_prog (prog:prog) (conf:config) : prog =
  { nodes = List.map cse_def prog.nodes }
