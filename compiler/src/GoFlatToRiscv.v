Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import riscv.util.Monads.
Require Import riscv.Utility.
Require Import riscv.Decode.
Require Import riscv.Memory.
Require Import riscv.Program.
Require Import riscv.RiscvMachine.
Require Import riscv.AxiomaticRiscv.
Require Import riscv.Run.
Require Import riscv.Execute.
Require Import coqutil.Tactics.Tactics.
Require Import compiler.containsProgram.
Require Import compiler.FlatToRiscvBitWidthSpecifics.
Require Import compiler.util.Tactics.

Local Unset Universe Polymorphism.

Section Go.

  Context {W: Words}.
  Context {RFF: RegisterFileFunctions Register word}.
  Context {Action: Type}.
  Context {mem: map.map word byte}.

  Local Notation RiscvMachineL := (RiscvMachine Register Action).

  Context {M: Type -> Type}.
  Context {MM: Monad M}.
  Context {RVM: RiscvProgram M word}.
  Context {RVS: @RiscvState M word _ _ RVM}.
  Context {RVAX: AxiomaticRiscv Action M}.
  Context {BWS: FlatToRiscvBitWidthSpecifics word}.

  Add Ring wring: (@word.ring_theory width word word_ok).

  Ltac ring' := unfold ZToReg, mul, add, MkMachineWidth.MachineWidth_XLEN in *; ring.

  Lemma go_left_identity{A: Type}: forall initialL post a
         (f : A -> M unit),
      mcomp_sat (f a) initialL post ->
      mcomp_sat (Bind (Return a) f) initialL post.
  Proof.
    intros. rewrite left_identity. assumption.
  Qed.

  Lemma go_right_identity: forall initialL post
         (m: M unit),
      mcomp_sat m initialL post ->
      mcomp_sat (Bind m Return) initialL post.
  Proof.
    intros. rewrite right_identity. assumption.
  Qed.

  Lemma go_associativity{A B: Type}: forall initialL post
         (m: M A)
         (f : A -> M B) (g : B -> M unit),
      mcomp_sat (Bind m (fun x : A => Bind (f x) g)) initialL post ->
      mcomp_sat (Bind (Bind m f) g) initialL post.
  Proof.
    intros. rewrite associativity. assumption.
  Qed.

  Lemma go_fetch_inst: forall {inst initialL pc0} (post: RiscvMachineL -> Prop),
      pc0 = initialL.(getPc) ->
      containsProgram initialL.(getMem) [inst] pc0 ->
      mcomp_sat (Bind (execute inst) (fun _ => step)) initialL post ->
      mcomp_sat (run1 (B := BitWidth)) initialL post.
  Proof.
    intros. subst.
    unfold run1.
    apply go_getPC.
    unfold containsProgram in H0.
    specialize (H0 0 _ eq_refl).
    unfold ldInst in *.
    destruct_one_match_hyp; [|discriminate].
    apply invert_Some_eq_Some in H0. subst inst.
    eapply go_loadWord; [|eassumption].
    match goal with
    | H: Memory.loadWord ?m ?pc = ?r |- Memory.loadWord ?m ?pc' = ?r =>
      replace pc' with pc; [exact H|]
    end.
    change (4 * 0) with 0. ring'.
  Qed.

End Go.
