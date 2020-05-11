open Basic_utils
open Usuba_AST
open Tp_AST
open Printf

(* true if bitslicing; false if vslicing *)
let bitslice = ref true

let ident_to_str (id:Usuba_AST.ident) : string =
  Str.global_replace (Str.regexp "'") "_" id.name

let rec arith_to_int (ae:Usuba_AST.arith_expr) : int =
  Utils.eval_arith_ne ae

let log_op_to_tp (op:Usuba_AST.log_op) : Tp_AST.log_op =
  match op with
  | And -> And
  | Or  -> Or
  | Xor -> Xor
  | _   -> assert false

let shift_op_to_tp (op:Usuba_AST.shift_op) : Tp_AST.shift_op =
  match op with
  | Lshift  -> Lshift
  | Rshift  -> Rshift
  | Lrotate -> Lrotate
  | Rrotate -> Rrotate
  | RAshift -> Printf.eprintf "Cannot generate arithmetic shifts for tightprove.\n";
               assert false

let rec var_to_tp (v:Usuba_AST.var) : string =
  match v with
  | Var v -> ident_to_str v
  | Index(v,e) -> sprintf "%s[%d]" (var_to_tp v) (arith_to_int e)
  | _ -> Printf.eprintf "Invalid var to convert to tp: %s\n"
                        (Usuba_print.var_to_str v);
         assert false
(* Warning: shadows above function *)
let var_to_tp (vars_corres: (string, Usuba_AST.var) Hashtbl.t)
              (v:Usuba_AST.var) : string =
  let tp_var = var_to_tp v in
  Hashtbl.add vars_corres tp_var v;
  tp_var

let rec expr_to_tp (vars_corres: (string, Usuba_AST.var) Hashtbl.t)
                   (e:Usuba_AST.expr) : Tp_AST.expr =
  match e with
  | Const(c,_)    -> if !bitslice then ConstAll c else Const c
  | ExpVar v      -> ExpVar(var_to_tp vars_corres v)
  | Not(ExpVar v) -> Not(var_to_tp vars_corres v)
  | Log(op,ExpVar x,ExpVar y) ->
     Log(log_op_to_tp op, var_to_tp vars_corres x, var_to_tp vars_corres y)
  | Shift(op,ExpVar e,ae)     ->
     Shift(shift_op_to_tp op, var_to_tp vars_corres e, arith_to_int ae)
  | Fun(f,[ExpVar v]) when f.name = "refresh" -> Refresh(var_to_tp vars_corres v)
  | e -> Printf.eprintf "expr_to_str: invalid expr `%s`\n"
                        (Usuba_print.expr_to_str e);
         assert false

let deq_to_tp (vars_corres: (string, Usuba_AST.var) Hashtbl.t)
              (deq:Usuba_AST.deq) : Tp_AST.asgn =
  match deq.content with
  | Eqn([lhs],e,_) ->
     { lhs = var_to_tp vars_corres lhs; rhs = expr_to_tp vars_corres e }
  | _ -> assert false

let rec vd_typ_to_tp (typ:Usuba_AST.typ) (acc:string) : string =
  match typ with
  | Uint(_,_,1)   -> sprintf "%s" acc
  | Uint(_,_,n)   -> sprintf "%s[%d]" acc n
  | Array(typ',n) -> vd_typ_to_tp typ' (sprintf "%s[%d]" acc (arith_to_int n))
  | _ -> assert false

let vd_to_tp (vd:Usuba_AST.var_d) : string =
  sprintf "%s%s" (ident_to_str vd.vd_id)
          (vd_typ_to_tp vd.vd_typ "")

let all_vars_same_m (var_l:Usuba_AST.var_d list) : bool =
  let first_m = Utils.get_type_m (List.hd var_l).vd_typ in
  List.for_all (fun vd -> Utils.get_type_m vd.vd_typ = first_m) var_l

let get_node_body (def:Usuba_AST.def) : Usuba_AST.deq list =
  match def.node with
  | Single(_,body) -> body
  | _ -> assert false

let m_as_int = function
  | Mint m -> m
  | _ -> assert false

let usuba_to_tp (def:Usuba_AST.def) : ((string,Usuba_AST.var) Hashtbl.t) * Tp_AST.def =
  assert (all_vars_same_m def.p_in);
  let m = m_as_int (Utils.get_type_m (List.hd def.p_in).vd_typ) in
  bitslice := m = 1;

  let vars_corres = Hashtbl.create 10 in

  let tp_def =
    { rs     = m;
      inputs = List.map vd_to_tp def.p_in;
      body   = List.map (deq_to_tp vars_corres) (get_node_body def) } in

  vars_corres, tp_def
