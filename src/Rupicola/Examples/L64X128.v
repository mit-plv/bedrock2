(* "LXM: Better Splittable Pseudorandom Number Generators (and Almost as Fast)"
   Guy L. Steele Jr. and Sebastiano Vigna, OOPSLA 2021. *)
(* Also at https://github.com/ocaml/ocaml/pull/10742/ *)

Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Arrays.
Require Import Rupicola.Lib.WordNotations.
From bedrock2 Require Import BasicC64Semantics.

Coercion co_word_of_Z := word.of_Z (word := word).
#[export] Hint Unfold co_word_of_Z : compiler_side_conditions.

Definition M : word :=
  word.of_Z 0xd1342543de82ef95.

Definition rotl (x: word) (k: Z) :=
  (x <<w word.of_Z k) |w (x >>w word.of_Z (64 - k)).

Definition lxm_next (a s: word) (x: list word) :=
  let/n x0 := ListArray.get x 0 in
  let/n z := s +w x0 in

  let/n z := (z ^w (z >>w 32)) *w 0xdaba0b6eb09322e3 in
  let/n z := (z ^w (z >>w 32)) *w 0xdaba0b6eb09322e3 in
  let/n z := (z ^w (z >>w 32)) in

  let/n s := s *w M +w a in

  let/n q0 := ListArray.get x 0 in
  let/n q1 := ListArray.get x 1 in
  let/n q1 := q1 ^w q0 in
  let/n q0 := rotl q0 24 in
  let/n q0 := q0 ^w q1 ^w (q1 <<w 16) in
  let/n q1 := rotl q1 37 in
  let/n x := ListArray.put x 0 q0 in
  let/n x := ListArray.put x 1 q1 in

  \< s, z, x \>.

Implicit Type R : mem -> Prop.
Instance spec_of_lxm_next : spec_of "lxm_next" :=
  fnspec! "lxm_next" a s xptr / x R ~> s' z,
  { requires tr mem :=
      (sizedlistarray_value AccessWord 2%nat xptr x ⋆ R) mem;
    ensures tr' mem' :=
      let '\<sn, zn, xn\> := lxm_next a s x in
      tr = tr' /\
      (sizedlistarray_value AccessWord 2 xptr xn ⋆ R) mem' /\
      s' = sn /\ z = zn  }.

Import SizedListArrayCompiler.
#[local] Hint Unfold rotl : compiler_cleanup.
#[local] Hint Extern 10 => lia : compiler_side_conditions.

Derive lxm_next_br2fn SuchThat
       (defn! "lxm_next"("a", "s", "x") ~> "s", "z" { lxm_next_br2fn },
        implements lxm_next)
       As lxm_next_br2fn_ok.
Proof.
  compile.
Qed.

Definition lxm_next_cbytes := Eval vm_compute in
  list_byte_of_string (ToCString.c_module [("dummy_main_for_static",([],[],cmd.skip)); lxm_next_br2fn]).
