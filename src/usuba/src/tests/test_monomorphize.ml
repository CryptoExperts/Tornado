open Usuba_AST
open Utils
open Monomorphize
open Parser_api

let test_specialize_shuffle_vslice () =
  let v   = fresh_ident "v" in
  let e   = Shuffle(Var v,[0; 3; 1; 2]) in
  let env = Hashtbl.create 1 in
  Hashtbl.add env v (Uint(Vslice,Mint 4,1));
  let expected = parse_expr "(v & 8:u<V>4) ^ ((v << 2) & 4:u<V>4) ^ ((v >> 1) & 2:u<V>4) ^ ((v >> 1) & 1:u<V>4)" in
  assert(Monomorphize.Vslice.specialize_expr (Hashtbl.create 1) (Hashtbl.create 1) env e = expected)



let test () =
  test_specialize_shuffle_vslice ()
