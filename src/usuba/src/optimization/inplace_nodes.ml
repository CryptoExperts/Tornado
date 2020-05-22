(***************************************************************************** )
                              inplace_nodes.ml

  Tries to make nodes modify their inputs in-place rather than
  creating new arrays everywhere.

( *****************************************************************************)

open Usuba_AST
open Basic_utils
open Utils


let rec can_inplace_deqs (deqs:deq list) : bool =
  List.for_all (fun deq ->
                match deq.content with
                | Eqn(lhs,e,_) ->
                   update_vars lhs;
                   check_eqn e
                | Loop(i,ei,ef,dl,_) -> t) deqs

                      (* M*)
let can_inplace_node (def:def) : bool =
  let
  match def.node with
  | Single(vars,body) ->
     let input_val =
     can_inplace_deqs def.p_in def.p_out body
  | _ -> false


let inplace_def (env_fun:(ident,def) Hashtbl.t) (def:def) : unit =
  ()

let run _ (prog:prog) (conf:config) : prog =
  let env_fun = build_env_fun prog.nodes in
  if conf.inplace_nodes then
    (List.iter (inplace_def env_fun) prog.nodes;
     { nodes = List.map (fun f -> Hashtbl.find env_fun f.id) prog.nodes })
  else prog


let as_pass = (run, "Inplace_nodes");
