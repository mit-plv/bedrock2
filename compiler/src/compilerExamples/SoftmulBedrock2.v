Require Import ZArith coqutil.Z.div_mod_to_equations.
Require Import bedrock2.NotationsCustomEntry.
Import Syntax BinInt String List.ListNotations ZArith.
Require Import coqutil.Z.Lia.
Require Import bedrock2Examples.rpmul.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

(* Variant of "ipow" implementing multiplication in terms of addition instead
* of exponentiation in terms of multiplication. *)

Definition softmul :=
  ("softmul", (["inst"; "a_regs"], @nil String.string, bedrock_func_body:(
  a = a_regs + ((inst>>$15)&$(Z.ones 5))<<$2;
  b = a_regs + ((inst>>$20)&$(Z.ones 5))<<$2;
  d = a_regs + ((inst>>$ 7)&$(Z.ones 5))<<$2;
  a = load(a);
  b = load(b);
  unpack! c = rpmul(a, b);
  store(d, c)
))).

From bedrock2 Require Import Semantics BasicC32Semantics WeakestPrecondition ProgramLogic.
From coqutil Require Import Word.Properties Word.Interface Tactics.letexists.
Require Import riscv.Spec.Decode riscv.Utility.Utility.
Require Import bedrock2.SepAutoArray bedrock2.SepAutoExports.
Open Scope bool_scope.

(* like (decode RV32I), but additionally also accepts the Mul instruction
   (but no other instructions from the M extension) *)
Definition mdecode(inst: Z): Instruction :=
  let opcode := bitSlice inst 0 7 in
  let rd := bitSlice inst 7 12 in
  let funct3 := bitSlice inst 12 15 in
  let rs1 := bitSlice inst 15 20 in
  let rs2 := bitSlice inst 20 25 in
  let funct7 := bitSlice inst 25 32 in
  if (opcode =? opcode_OP) && (funct3 =? funct3_MUL) && (funct7 =? funct7_MUL)
  then MInstruction (Mul rd rs1 rs2)
  else decode RV32I inst.

Definition idecode: Z -> Instruction := decode RV32I.

#[export] Instance spec_of_softmul : spec_of "softmul" :=
  fnspec! "softmul" inst a_regs / rd rs1 rs2 regvals R,
  { requires t m :=
      mdecode (word.unsigned inst) = MInstruction (Mul rd rs1 rs2) /\
      List.length regvals = 32%nat /\
      sep (a_regs :-> regvals : word_array) R m;
      (* Alternative way of expressing the length constraint:
      sep (a_regs |-> with_len 32 word_array regvals) R m; *)
    ensures t' m' :=
      t = t' /\
      sep (a_regs :-> List.upd regvals (Z.to_nat rd) (word.mul
               (List.nth (Z.to_nat rs1) regvals default)
               (List.nth (Z.to_nat rs2) regvals default)) : word_array) R m'
 }.

Lemma decode_RV32I_not_MInstruction i mi : decode RV32I i <> MInstruction mi.
Proof.
  cbv beta delta [decode].
  repeat lazymatch goal with
         | |- (let x := ?a in ?b) <> ?c =>
             change (let x := a in b <> c); intro
         | x := ?t : ?T |- _ =>
             pose proof (eq_refl t : x = t); clearbody x
         end.
  destruct_one_match. 1: clear; congruence.
  clear -H H0 H8.
  subst. cbn.
  destruct_one_match; cbn. 1: clear; congruence.
  destruct_one_match; cbn; congruence.
Qed.

Lemma softmul_ok : program_logic_goal_for_function! softmul.
Proof.
  repeat straightline.

  cbv [mdecode] in *.
  case (_&&_) eqn:? in *; cycle 1; [|clear Heqb0].
  { edestruct decode_RV32I_not_MInstruction; eauto. }
  set (word.unsigned inst) as w in *; inversion H0; clear H0; cbv [bitSlice] in *;subst w.
  repeat match goal with H : context G [?e] |- _ =>
    let e' := groundcbv.groundcbv e in
    let H' := context G[e'] in
    progress change H' in H
  end.
  repeat match goal with
    | x := ?v |- _ =>
        idtac x;
        let H := fresh "H" x in
        pose proof (eq_refl x : x = v) as H; move H before x; clearbody x; move x at top
    end.
  1:rewrite <-(word.of_Z_unsigned (word.and _ _)), ?word.unsigned_and_nowrap, ?word.unsigned_sru_nowrap, ?unsigned_sru_nowrap, 2word.unsigned_of_Z_nowrap, H4 in Hd.
  1:rewrite <-(word.of_Z_unsigned (word.and _ _)), ?word.unsigned_and_nowrap, ?word.unsigned_sru_nowrap, ?unsigned_sru_nowrap, 2word.unsigned_of_Z_nowrap, H5 in Ha.
  1:rewrite <-(word.of_Z_unsigned (word.and _ _)), ?word.unsigned_and_nowrap, ?word.unsigned_sru_nowrap, ?unsigned_sru_nowrap, 2word.unsigned_of_Z_nowrap, H6 in Hb.
  all:[> | rewrite ?word.unsigned_of_Z_nowrap; clear; blia .. ].

  change (31) with (Z.ones 5) in *.
  rewrite !Z.land_ones in * by better_lia.

  eexists; split.
  { eexists; split; repeat straightline.
    eexists; split; repeat straightline.
    eapply Scalars.load_word_of_sep.
    match goal with
    | |- (Scalars.scalar ?a ?v * ?b)%sep ?m => change (sep (a :-> v : Scalars.scalar) b m)
    end.
    scancel_asm. }

  repeat straightline.

  eexists; split.
  { eexists; split; repeat straightline.
    eexists; split; repeat straightline.
    eapply Scalars.load_word_of_sep.
    match goal with
    | |- (Scalars.scalar ?a ?v * ?b)%sep ?m => change (sep (a :-> v : Scalars.scalar) b m)
    end.
    scancel_asm. }

  repeat (straightline || straightline_call).

  eapply Scalars.array_store_of_sep with (sz:=access_size.word) (n:=Z.to_nat rd) (size:=word.of_Z 4%Z).
  { subst d. f_equal. ZnWords. }
  { use_sep_assumption; cbn [seps]; unfold word_array.
    reflexivity. }
  { ZnWords. }

  intro_new_mem.
  repeat straightline; ssplit; trivial.
  use_sep_assumption; cbn [seps]; unfold word_array.

  rewrite <-!Z.land_ones in * by better_lia.
  Morphisms.f_equiv.
  Morphisms.f_equiv.
  f_equal.
  { subst rd. reflexivity. }
  eapply word.unsigned_inj; rewrite H8, word.unsigned_mul, Z.land_ones by (clear;blia).
  cbv [a b]; subst rs1; subst rs2; rewrite !word.word_sub_add_l_same_l.
  cbv [word.wrap].
  repeat match goal with |- context G [Z.lnot ?e] =>
    let e' := groundcbv.groundcbv (Z.lnot e) in
    let H' := context G[e'] in
    progress change H'
  end.
  rewrite !Z.land_ones, !(Z.land_ones _ 5) by (clear;blia).
  do 5 f_equal.
  all:ZnWords.

  Unshelve.
  all : exact (word.of_Z 0).
Qed.
