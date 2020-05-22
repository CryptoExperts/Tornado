open Usuba_AST
open Basic_utils
open Utils
open Pass_runner

let run (runner:pass_runner) (prog:prog) (conf:config) =
  runner#run_modules [ Expand_array.as_pass;
                       Normalize_inner_core.as_pass;
                       Expand_parameters.as_pass;
                       Fix_dim.Dir_params.as_pass;
                       Expand_array.as_pass;
                       Normalize_inner_core.as_pass;
                       Expand_parameters.as_pass;
                       Fix_dim.Dir_inner.as_pass;
                       Expand_array.as_pass;
                       Normalize_inner_core.as_pass ] prog

let as_pass = (run, "Normalize_core")
