Require Import bedrock2.NotationsCustomEntry.

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition uint128_add : func :=
  ("uint128_add", (["s"; "a"; "b"], ["c"], bedrock_func_body:(
  a0 = load4(a); a = a+$4;
  b0 = load4(b); b = b+$4;
  a1 = load4(a); a = a+$4;
  b1 = load4(b); b = b+$4;
  a2 = load4(a); a = a+$4;
  b2 = load4(b); b = b+$4;
  a3 = load4(a);
  b3 = load4(b);

  s0 = a0 + b0;
  c1 = s0 < a0;
  store4(s, s0); s = s+$4;

  s1 = a1 + b1;
  c2 = s1 < a1;
  s1 = c1 + s1;
  c2p = s1 < c1;
  c2 = c2 + c2p;
  store4(s, s1); s = s+$4;

  s2 = a2 + b2;
  c3 = s2 < a2;
  s2 = c2 + s2;
  c3p = s2 < c2;
  c3 = c3 + c3p;
  store4(s, s2); s = s+$4;

  s3 = a3 + b3;
  c  = s3 < a3;
  s3 = c3 + s3;
  c4p = s3 < c3;
  c = c + c4p;
  store4(s, s3)
))).

Require Import bedrock2.FE310CSemantics bedrock2.Semantics .
Require Import bedrock2.WeakestPrecondition bedrock2.ProgramLogic.
Require Import coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface bedrock2.Map.SeparationLogic.
Require Import bedrock2.Array bedrock2.Scalars.
Require Import bedrock2.ZnWords.

Section WithParameters.
  Context {word: word.word 32} {mem: map.map word Byte.byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.
  Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing) (* experiment*).
  Import ProgramLogic.Coercions.
  Let eval : list word -> Z :=
    List.fold_right (fun a s => word.unsigned a + 2^32*s) 0.

  Instance spec_of_swap : spec_of "uint128_add" :=
    fnspec! "uint128_add" ps pa pb / a b s R Ra Rb ~> c,
    { requires t m :=
        m =* array scalar32 (word.of_Z 4) pa a * Ra /\
        m =* array scalar32 (word.of_Z 4) pb b * Rb /\
        m =* array scalar32 (word.of_Z 4) ps s * R /\
        length a = 4%nat /\ length b = 4%nat /\ length s = 4%nat;
      ensures t' m' := t=t' /\
        exists s, length s = 4%nat /\
        m' =* array scalar32 (word.of_Z 4) ps s * R /\
        2^128*c + eval s = eval a + eval b
    }.

  Lemma linear_carry (a b : word)
    (s : word := word.add a b)
    (c : word := if word.ltu s a then word.of_Z 1 else word.of_Z 0)
    : s + 2^32 * c = a + b /\ 0 <= c <= 1.
  Proof.
    clear -word_ok.
    intros.
    subst s c.
    pose proof Properties.word.unsigned_range a.
    pose proof Properties.word.unsigned_range b.
    erewrite !word.unsigned_ltu.
    rewrite ?word.unsigned_add; cbv [word.wrap];
    destr.destr ((a + b) mod 2^32 <? a);
    rewrite ?Properties.word.unsigned_of_Z_1, ?Properties.word.unsigned_of_Z_0;
    Tactics.ssplit; try (PreOmega.Z.div_mod_to_equations; Lia.nia).
  Qed.

  Lemma uint128_add_ok : program_logic_goal_for_function! uint128_add.
  Proof.
    repeat straightline.

    do 4 (destruct a; [inversion H2|]); destruct a; inversion H2.
    do 4 (destruct b; [inversion H3|]); destruct b; inversion H3.
    do 4 (destruct s; [inversion H4|]); destruct s; inversion H4.
    rename r into a0'; rename r0 into a1'; rename r1 into a2'; rename r2 into a3'.
    rename r3 into b0'; rename r4 into b1'; rename r5 into b2'; rename r6 into b3'.
    cbn [array length] in *. clear H2 H3 H4.


    repeat straightline.

    eexists; Tactics.ssplit; trivial.
    eexists [_;_;_;_]; split; cbn [array]; trivial.
    split; [ecancel_assumption|].

    cbn [eval List.fold_right]; rewrite !Z.mul_0_r, !Z.add_0_r.
    repeat match goal with
           | c := if word.ltu ?s _ then _ else _ |- _ =>
               pose proof (linear_carry _ _ : s + 2^32 * c = _ /\ _ <= c <= _); revert dependent s
           end.
           clear -word_ok.
    intros; ZnWords.
  Qed.
End WithParameters.
