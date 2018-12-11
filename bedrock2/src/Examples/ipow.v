Require Import coqutil.Z.div_mod_to_equations.
Require Import bedrock2.BasicC64Syntax bedrock2.NotationsInConstr.
Import BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Existing Instance bedrock2.BasicC64Syntax.Basic_bopnames_params.
Local Coercion literal (z : Z) : Syntax.expr := Syntax.expr.literal z.
Local Coercion var (x : string) : Syntax.expr := Syntax.expr.var x.

Definition ipow := ("ipow", (["x";"e"], (["ret"]:list varname), bedrock_func_body:(
  "ret" = 1;;
  while ("e") {{
    "t" = "e" .& 1;;
    if ("t") {{ "ret" = "ret" * "x" }};;
    "e" = "e" >> 1;;
    "x" = "x" * "x";;
    Syntax.cmd.unset "t"
  }}
))).

Require Import Coq.micromega.Lia.
Local Ltac mia := Z.div_mod_to_equations; nia.

Require Import bedrock2.BasicC64Semantics coqutil.Word.Interface.
Require bedrock2.WeakestPrecondition coqutil.Word.Properties.

Definition spec_of_ipow := fun functions =>
  forall x e t m,
    WeakestPrecondition.call (fun _ => True) (fun _ => False) (fun _ _ => False) functions
      "ipow" t m [x; e]
      (fun t' m' rets => t=t'/\ m=m' /\ exists v, rets = [v] /\ (
        word.unsigned x ^ word.unsigned e < 2^64 ->
        word.unsigned v = word.unsigned x ^ word.unsigned e)).

From coqutil.Tactics Require Import letexists eabstract.
Require Import bedrock2.ProgramLogic.
Require Import AdmitAxiom.
Lemma ipow_ok : forall functions, spec_of_ipow (ipow::functions).
Proof.
  bind_body_of_function ipow; cbv [spec_of_ipow].
  intros.
  hnf. (* incoming call dispatch *)
  letexists. split. exact eq_refl. (* argument initialization *)

  repeat straightline; show_program.

  Import Word.Properties.word Word.Interface.word.
  refine (TailRecursion.tailrec HList.polymorphic_list.nil ["e";"ret";"x"]
    (fun v t m e ret x => PrimitivePair.pair.mk (v = word.unsigned e)
    (fun t' m' e' ret' x' => t' = t /\ m' = m /\
       (unsigned ret * unsigned x ^ unsigned e < 2^64 ->
        unsigned ret' = unsigned ret * unsigned x ^ unsigned e)))
    (fun n m => 0 <= n < m)
    _ _ tt _ _ _);

    cbn [HList.hlist.foralls HList.tuple.foralls
         HList.hlist.existss HList.tuple.existss
         HList.hlist.apply  HList.tuple.apply
         HList.hlist
         List.repeat Datatypes.length
         HList.polymorphic_list.repeat HList.polymorphic_list.length
         PrimitivePair.pair._1 PrimitivePair.pair._2] in *.

  { repeat straightline. }
  { exact (Z.lt_wf _). }
  { repeat straightline. } (* init precondition *)
  { (* loop test *)
    repeat straightline; try show_program.
    { (* loop body *)
      letexists; split; [eabstract (repeat straightline)|]. (* if condition *)
      split. (* if cases, path-blasting *)
      { repeat straightline.
        { (* measure decreases *)
          cbn [parameters Semantics.interp_binop Basic_bopnames.interp_binop Semantics.width] in *.
          unshelve (idtac; let pf := open_constr:(unsigned_range _ x0) in pose proof pf);
            [exact _|cbv; congruence|].
          repeat match goal with
                   |- context [?x] => subst x
                 end.
          rewrite ?unsigned_sru_nowrap,
                  ?unsigned_of_Z,
                  ?Z.shiftr_div_pow2
            by (cbv; congruence).
          change Semantics.width with 64 in *.
          change (2 ^ (1 mod 2 ^ 64)) with 2.
          mia. }
        { (* invariant preserved *)
          repeat split; try exact eq_refl; intros.
          cbn [parameters Semantics.interp_binop Basic_bopnames.interp_binop Semantics.width] in *.
          replace (unsigned x0) with (2 * (unsigned x0 / 2) + 1) in * by (subst v1; revert H0; admit).
          rewrite ?Z.pow_add_r, Z.pow_twice_r, ?Z.pow_1_r, ?Z.pow_mul_l, ?Z.mul_assoc in * by ((intro;discriminate)||admit).
          rewrite H3; cycle 1;
            repeat match goal with
                     |- context [?x] => subst x
                   end;
            repeat rewrite ?unsigned_of_Z,
                           ?unsigned_sru_nowrap,
                           ?unsigned_mul,
                           ?Z.mul_mod_idemp_l,
                           ?Z.shiftr_div_pow2;
            change Semantics.width with 64 in *;
            change (1 mod 2 ^ 64) with 1; change (2^1) with 2; try Lia.lia.
          { rewrite !Z.mod_small by (revert H1; admit). rewrite Z.pow_mul_l. abstract mia. }
          { rewrite !Z.mod_small by (revert H1; admit). rewrite Z.pow_mul_l. abstract ring. } } }
      {
        straightline; [].
        straightline; [].
        straightline; [].
        (* repeat straightline. *)
        (* Error: Anomaly "Universe Top.196 undefined." Please report at http://coq.inria.fr/bugs/. *)
        straightline; [].
        repeat straightline.
        { (* measure decreases *)
          cbn [parameters Semantics.interp_binop Basic_bopnames.interp_binop Semantics.width] in *.
          unshelve (idtac; let pf := open_constr:(unsigned_range _ x0) in pose proof pf);
            [exact _|cbv; congruence|].
          repeat match goal with
                   |- context [?x] => subst x
                 end.
          rewrite ?unsigned_sru_nowrap,
                  ?unsigned_of_Z,
                  ?Z.shiftr_div_pow2
            by (cbv; congruence).
            change Semantics.width with 64 in *;
          change (2 ^ (1 mod 2 ^ 64)) with 2.
          mia. }
        { (* invariant preserved *)
          repeat split; try exact eq_refl; intros.
          cbn [parameters Semantics.interp_binop Basic_bopnames.interp_binop Semantics.width] in *.
          replace (unsigned x0) with (2 * (unsigned x0 / 2)) in * by (subst v1; revert H0; admit).
          rewrite ?Z.pow_add_r, Z.pow_twice_r, ?Z.pow_1_r, ?Z.pow_mul_l, ?Z.mul_assoc in *.
          rewrite H3; cycle 1;
            repeat match goal with
                     |- context [?x] => subst x
                   end;
            repeat rewrite ?word.unsigned_of_Z,
                           ?unsigned_sru_nowrap,
                           ?unsigned_mul,
                           ?Z.mul_mod_idemp_l,
                           ?Z.shiftr_div_pow2;
            change Semantics.width with 64 in *;
            change (1 mod 2 ^ 64) with 1; change (2^1) with 2; try Lia.lia.
          { rewrite !Z.mod_small by (revert H1; admit). rewrite Z.pow_mul_l. abstract mia. }
          { rewrite !Z.mod_small by (revert H1; admit). rewrite Z.pow_mul_l. abstract ring. } } } }
    { (* end of loop *)
      repeat split; intros.
      replace (unsigned x0) with 0 in * by (revert H; admit).
      rewrite Z.pow_0_r, Z.mul_1_r. exact eq_refl. } }

  repeat straightline.

  (* function postcondition *)
  repeat eapply conj; try exact eq_refl.
  letexists. split. exact eq_refl.
  intros.
  repeat match goal with
           |- context [?x] => subst x
         end.
  subst v. rewrite ?unsigned_of_Z, ?Z.mul_1_l in *.
  rewrite H1; trivial.

  Unshelve. (* WHY does this not get admits? *)

  Grab Existential Variables.

(* 11 subgoals (ID 6265) *)
(*  word_test x0 = false -> 0 = unsigned x0 *)
(*  unsigned x1 * unsigned x2 ^ (unsigned x0 / 2) * unsigned x2 ^ (unsigned x0 / 2) < 2 ^ 64 -> 0 <= unsigned x2 * unsigned x2 < 2 ^ 64 *)
(*  unsigned x1 * unsigned x2 ^ (unsigned x0 / 2) * unsigned x2 ^ (unsigned x0 / 2) < 2 ^ 64 -> 0 <= unsigned x2 * unsigned x2 < 2 ^ 64 *)
(*  word_test (and x0 (of_Z 1)) = false -> 2 * (unsigned x0 / 2) = unsigned x0 *)
(*  unsigned x1 * unsigned x2 ^ (unsigned x0 / 2) * unsigned x2 ^ (unsigned x0 / 2) * unsigned x2 < 2 ^ 64 -> 0 <= unsigned x2 * unsigned x2 < 2 ^ 64 *)
(*  unsigned x1 * unsigned x2 ^ (unsigned x0 / 2) * unsigned x2 ^ (unsigned x0 / 2) * unsigned x2 < 2 ^ 64 -> 0 <= unsigned x1 * unsigned x2 < 2 ^ 64 *)
(*  unsigned x1 * unsigned x2 ^ (unsigned x0 / 2) * unsigned x2 ^ (unsigned x0 / 2) * unsigned x2 < 2 ^ 64 -> 0 <= unsigned x2 * unsigned x2 < 2 ^ 64 *)
(*  unsigned x1 * unsigned x2 ^ (unsigned x0 / 2) * unsigned x2 ^ (unsigned x0 / 2) * unsigned x2 < 2 ^ 64 -> 0 <= unsigned x1 * unsigned x2 < 2 ^ 64 *)
(*  0 <= 2 * (unsigned x0 / 2) *)
(*  0 <= 2 * (unsigned x0 / 2) *)
(*  word_test (and x0 (of_Z 1)) = true -> 2 * (unsigned x0 / 2) + 1 = unsigned x0 *)

Defined.