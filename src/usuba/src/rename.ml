(***************************************************************************** )
                                 rename.ml

    This module renames every use defined variable or node, in order to avoid
    any name conflict with variables that the compiler may introduce, or
    variables that result of the expansion of array or uint_n.
    More precisely, we add a quote at the end of every user-defined name. We
    chose quotes because they aren't allowed to be part of variables names in
    Usuba.

    After this module has ran, every user-defined variable or module should
    have its name ending with a quote (').

( *****************************************************************************)


open Usuba_AST
open Basic_utils
open Utils

(* Since the transformation of the code will produce new variable names,
   we must rename the old variables to make there won't be any conflicts
   with those new names (or with any ocaml builtin name).
   Basically, it means adding an "'" at the end of every identifier name. *)

let rec rename_arith_expr (e:arith_expr) =
  match e with
  | Const_e c -> Const_e c
  | Var_e v -> Var_e (fresh_suffix v "'")
  | Op_e(op,x,y) -> Op_e(op,rename_arith_expr x,rename_arith_expr y)

let rec rename_var (v:var) =
  match v with
  | Var v -> Var (fresh_suffix v "'")
  | Index(v,e) -> Index(rename_var v,rename_arith_expr e)
  | Range(v,ei,ef) -> Range(rename_var v,rename_arith_expr ei,rename_arith_expr ef)
  | Slice(v,l) -> Slice(rename_var v,List.map rename_arith_expr l)

let rec rename_expr (e:expr) =
  match e with
  | Const(c,t) -> Const(c,t)
  | ExpVar v -> ExpVar (rename_var v)
  | Tuple l  -> Tuple(List.map rename_expr l)
  | Log(op,x,y) -> Log(op,rename_expr x,rename_expr y)
  | Shuffle(v,l) -> Shuffle(rename_var v,l)
  | Arith(op,x,y) -> Arith(op,rename_expr x,rename_expr y)
  | Shift(op,x,y) -> Shift(op,rename_expr x,rename_arith_expr y)
  | Not e -> Not (rename_expr e)
  | Fun(f,l) -> if is_builtin f then Fun(f,List.map rename_expr l)
                else Fun(fresh_suffix f "'",List.map rename_expr l)
  | Fun_v(f,e,l) -> Fun_v(fresh_suffix f "'",rename_arith_expr e,List.map rename_expr l)
  | Fby(ei,ef,f)   -> Fby(rename_expr ei,rename_expr ef,
                          match f with
                          | None -> None
                          | Some id -> Some (fresh_suffix id "'"))
  | When(e,c,x) -> When(rename_expr e,c,fresh_suffix x "'")
  | Merge(x,l)  -> Merge(fresh_suffix x "'",List.map (fun (c,e) -> c,rename_expr e) l)



let rec rename_pat pat =
  List.map rename_var pat

let rec rename_deq deqs =
    List.map (fun d -> { d with content = match d.content with
                         | Eqn(pat,expr,sync) ->
                            Eqn(rename_pat pat,rename_expr expr,sync)
                         | Loop(id,ei,ef,d,opts) ->
                            Loop(fresh_suffix id "'",ei,ef,rename_deq d,opts) }) deqs

let rec rename_p (p:p) =
  List.map (fun vd -> { vd with vd_id = fresh_suffix vd.vd_id "'" } ) p

let rename_def (def:def) : def =
  { id    = fresh_suffix def.id "'";
    p_in  = rename_p def.p_in;
    p_out = rename_p def.p_out;
    opt   = def.opt;
    node = match def.node with
           | Single (p_var, body) ->
              Single(rename_p p_var, rename_deq body)
           | Multiple nodes ->
              Multiple(List.map (fun node -> match node with
                                             | Single(vars,body) -> Single(rename_p vars, rename_deq body)
                                             | _ -> node) nodes)
           | _ -> def.node }


let rename_prog (p: prog) (conf:config) : prog =
  { nodes = List.map rename_def p.nodes }
