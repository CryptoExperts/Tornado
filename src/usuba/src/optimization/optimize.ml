open Basic_utils
open Utils
open Usuba_AST
open Usuba_print
open Pass_runner

(* Clean.clean_vars_decl removes unused variables from variable declarations of nodes
   (unused variables will likely be variables that have been optimized out) *)
module Clean = struct

  let rec clean_var env (var:var) : unit =
    match var with
    | Var id -> Hashtbl.replace env id 1
    | Index(v,_)
    | Range(v,_,_) | Slice(v,_) -> clean_var env v

  let rec clean_expr env (e:expr) : unit =
    match e with
    | ExpVar(v) -> clean_var env v
    | Tuple l -> List.iter (clean_expr env) l
    | Not e -> clean_expr env e
    | Shift(_,x,_) -> clean_expr env x
    | Log(_,x,y) -> clean_expr env x; clean_expr env y
    | Arith(_,x,y) -> clean_expr env x; clean_expr env y
    | Fun(_,l) -> List.iter (clean_expr env) l
    | Fun_v(_,_,l) -> List.iter (clean_expr env) l
    | _ -> ()

  let clean_in_deqs (vars:p) (deqs:deq list) : p =
    let env = Hashtbl.create 100 in
    let rec aux d = match d.content with
      | Eqn(l,e,_) -> List.iter (clean_var env) l;
                      clean_expr env e
      | Loop(_,_,_,d,_) -> List.iter aux d in
    List.iter aux deqs;
    List.sort_uniq (fun a b -> compare a b)
                   ( List.filter (fun vd -> match Hashtbl.find_opt env vd.vd_id with
                                            | Some _ -> true
                                            | None -> false) vars)

  let clean_def (def:def) : def =
    match def.node with
    | Single(vars,body) ->
       let vars = clean_in_deqs vars body in
       { def with node = Single(vars,body) }
    | _ -> def

  let run _ (prog:prog) (conf:config) : prog =
    { nodes = List.map clean_def prog.nodes }


  let as_pass = (run, "Clean")
end



let optimize (runner:pass_runner) (prog: Usuba_AST.prog) (conf:config) : Usuba_AST.prog =


  runner#run_modules_guard
           [ Interleave.as_pass, conf.interleave > 0;
             Simple_opts.as_pass, true;
             Fuse_loop_general.as_pass, conf.loop_fusion;
             Simple_opts.as_pass, true;
             Scheduler.as_pass,  conf.scheduling;
             Share_var.as_pass,  conf.share_var;
             Clean.as_pass, true;
             Remove_dead_code.as_pass, true ] prog


let as_pass = (optimize, "Optimize")
