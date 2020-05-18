(***************************************************************************** )
                              init_scheduler.ml

  Schedule the equations of each nodes according to their dependencies.
  (basically, it "imperativize" the code)

  This algorithm is not an optimization: each equation is considered as it comes:
  if its dependencies are ready, then it is scheduled, otherwise it will be scheduled
  later.

( *****************************************************************************)



open Usuba_AST
open Basic_utils
open Utils


(* Expands a variable, keeping it's intermediary expensions.
   For instance, if x:bool[2][3], then we'll get:
     (x, x[0], x[1], x[0][0], x[0][1], ...)
 *)
let rec expand_var_w_inter env_var (v:var) : var list =
  match get_var_type env_var v with
  | Nat         -> [ v ]
  | Uint(_,_,1) -> [ v ]
  | _ -> v :: (flat_map (expand_var_w_inter env_var) (expand_var_partial env_var v))

(* Expands each var of 'vars' and adds it to the table 'ready' *)
let update_ready (ready:(var,bool) Hashtbl.t)
                 (env_var:(ident,typ) Hashtbl.t)
                 (vars:var list) : unit =
  List.iter (fun v -> List.iter (fun v' -> Hashtbl.add ready v' true)
                                (expand_var_w_inter env_var v)) vars


(* Updates to_sched, which is a hash of hash (see comment in schedule_deqs) *)
let update_to_sched (to_sched:(var,(deq,bool) Hashtbl.t) Hashtbl.t)
                    (v:var) (deq:deq) : unit =
  match Hashtbl.find_opt to_sched v with
  | Some h -> Hashtbl.replace h deq true
  | None   -> let h = Hashtbl.create 10 in
              Hashtbl.replace h deq true;
              Hashtbl.replace to_sched v h

(* Returns true if 'v' is ready (ie, its definition has been scheduled).
   It's a bit tricky in the case of array.
   For instance, if x:bool[2][3], then x[2] is ready if
     - 'x' has been scheduled
     - x[0], and x[1] has been scheduled.
       And reccursively on x[0] and x[1]
       (x[0] has been scheduled, or x[0][0],x[0][1],x[0][2]...)
*)
let rec is_ready (env_var:(ident,typ) Hashtbl.t)
                 (ready:(var,bool) Hashtbl.t)
                 (v:var) : bool =
  (* Looks if sub-variables of v have been scheduled
     ie. (x[0], x[1]) instead of x *)
  let rec is_ready_bot (v:var) : bool =
    match Hashtbl.mem ready v with
    | true  -> true
    | false ->
       let expanded = expand_var_partial env_var v in
       match expanded with
       | [ v' ] when v' = v -> false
       | _ -> List.for_all is_ready_bot expanded in

  (* Looks if parent-variable have been scheduled
     ie. x instead of x[0] *)
  let rec is_ready_top (v:var) : bool =
    match Hashtbl.mem ready v with
    | true  -> true
    | false ->
       match v with
       | Var _       -> false
       | Index(v',_) -> is_ready_top v'
       | _ -> assert false in

  (is_ready_bot v) || (is_ready_top v)

let schedule_deqs (env_var:(ident, typ) Hashtbl.t) (def:def) (deqs:deq list) : deq list =
  let ready = Hashtbl.create 100 in
  update_ready ready env_var (p_to_vars def.p_in);

  (* The list of instruction scheduled *)
  let body : deq list ref = ref [] in
  (* The instructions to schedule: a hash of hash:
      { x => { deq1 => true, deq2 => true }}
     means that deq1 and deq2 need to be scheduled once x has been computed
     (because deq1 and deq2 use x) *)
  let to_sched : (var,(deq,bool) Hashtbl.t) Hashtbl.t = Hashtbl.create 100 in
  (* A hash of the instructions already scheduled *)
  let sched : (deq,bool) Hashtbl.t = Hashtbl.create 100 in

  (* 'v' have been scheduled; 'propagate' will try to schedule equations that
     were depending on 'v' *)
  let rec propagate (v:var) : unit =
    (* try to schedule v[0], v[1], etc. *)
    let rec propagate_bot (v:var) =
      if not (Hashtbl.mem ready v) then
        begin
          if Hashtbl.mem to_sched v then
            Hashtbl.filter_map_inplace
              (fun deq' _ -> match sched_it deq' with
                             | true  -> None
                             | false -> Some true) (Hashtbl.find to_sched v);
          let expanded = expand_var_partial env_var v in
          match expanded with
          | [ v' ] when v' = v -> ()
          | _ -> List.iter propagate_bot expanded
        end in

    (* if v is actually v'[x], tries to schedule v', iff all of it's components are ready *)
    let rec propagate_top (v:var) =
      if not (Hashtbl.mem ready v) then
        begin
          if Hashtbl.mem to_sched v then
            Hashtbl.filter_map_inplace
              (fun deq' _ -> match sched_it deq' with
                             | true  -> None
                             | false -> Some true) (Hashtbl.find to_sched v);
          match v with
          | Var _ -> ()
          | Index(v',_) ->
             if List.for_all (fun x -> Hashtbl.mem ready x)
                             (expand_var_partial env_var v') then
               propagate_top v'
          | _ -> assert false
        end in

    propagate_bot v;
    propagate_top v

  (* Tries to schedule an instruction.
     Returns true if the instruction was scheduled,
     false otherwise (ie, it's dependencies aren't scheduled yet) *)
  and sched_it (deq:deq) : bool =
    match Hashtbl.find_opt sched deq with
    | Some _ -> true
    | None ->
       match deq.content with
       | Eqn(lhs,e,sync) ->
          let used_vars : var list = get_used_vars e in
          if List.for_all (is_ready env_var ready) used_vars then
            begin
              body := deq :: !body;
              update_ready ready env_var lhs;
              Hashtbl.replace sched deq true;
              List.iter propagate lhs;
              List.iter (fun v ->
                         match Hashtbl.find_opt to_sched v with
                         | Some h ->
                            Hashtbl.filter_map_inplace
                              (fun deq' _ ->
                               match sched_it deq' with
                               | true  -> None
                               | false -> Some true) h
                         | None -> ())
                        (flat_map (expand_var_w_inter env_var) lhs);
              true
            end
          else (* dependencies not ready *)
            (List.iter (fun v -> update_to_sched to_sched v deq) used_vars;
             false)
       | Loop _ -> Printf.printf "Unexpected loop when scheduling %s.\n" def.id.name;
                   assert false in

  ignore(List.map sched_it deqs);

  if List.length !body <> List.length deqs then
    (
      let hash = Hashtbl.create 1000 in
      List.iter (fun x -> Hashtbl.add hash x true) !body;
      List.iter (fun x -> match Hashtbl.find_opt hash x with
                          | Some _ -> ()
                          | None -> Printf.printf "Didn't schedule %s\n"
                                                  (Usuba_print.deq_to_str x)) deqs;
      raise (Error (Printf.sprintf "Couldn't find a valid scheduling. (%s)" def.id.name))
    )
  else
    List.rev !body



let schedule_def (def:def) : def =
  { def with
    node = match def.node with
           | Single(vars,body) ->
              let env_var = build_env_var def.p_in def.p_out vars in
              Single(vars,schedule_deqs env_var def body)
           | _ -> def.node }

(* Must be called once arrays (and thus Loop) have been removed. *)
let run _ (prog:prog) (conf:config): prog =
  (* Printf.fprintf stderr "Scheduler (simple) disabled.\n"; *)
  (* if conf.unroll then *)
  (* { nodes = List.map schedule_def prog.nodes } *)
  (* else *)
    prog


let as_pass = (run, "Init_scheduler")
