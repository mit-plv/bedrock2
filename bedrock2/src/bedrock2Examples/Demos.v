From Coq Require Import BinInt String List. Import ListNotations.
Require Import coqutil.Macros.subst coqutil.Macros.unique bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.
Require Import coqutil.sanity.

Local Open Scope Z_scope. Local Open Scope list_scope. Local Open Scope string_scope.

Definition bsearch := func! (left, right, target) ~> left {
  while (right - left) {
    mid = left + (((right-left) >> $4) << $3);
    if (load(mid) < target) {
      left = mid + $8
    } else {
      right = mid
    };
    coq:(cmd.unset "mid")
  }
}.

(* input_base is an address fixed at compile time *)
Definition listsum (input_base: Z) := func! () ~> sumreg {
  sumreg = $0;
  n = load4(input_base);
  i = $0;
  while (i < n) {
    a = load4(coq:(input_base + 4) + (i << $2));
    sumreg = sumreg + a;
    i = i + $1
  }
}.

(* input_base is an address fixed at compile time *)
Definition fibonacci(n: Z) := func! () ~> b {
  a = $0;
  b = $1;
  i = $0;
  while (i < n) {
    c = a + b;
    a = b;
    b = c;
    i = i + $1
  }
}.

Definition fibonacciServer (n_load_addr n_store_addr: Z) := func! () ~> b {
  n = load4(n_load_addr);
  a = $0;
  b = $1;
  i = $0;
  if (n < $47) {
    while (i < n) {
      c = a + b;
      a = b;
      b = c;
      i = i + $1
    }
  } else {
    b = $-1
  };
  store4(n_store_addr, b)
}.

Definition dummy := func! { /*skip*/ }.

Definition allProgs: list (string*func) :=
  Eval unfold bsearch, listsum, fibonacci in
    [("bsearch",bsearch); ("listsum1024",listsum 1024); ("fibonacci6",fibonacci 6)].

(*
Print allProgs.
*)

Require Import bedrock2.ToCString.
Definition allProgsAsCString : string :=
  Eval cbv in c_module allProgs.

(*
Print allProgsAsCString.
*)
