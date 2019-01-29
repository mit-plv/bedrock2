Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
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
Require Import riscv.proofs.DecodeEncode.
Require Import coqutil.Tactics.Tactics.
Require Import compiler.util.Tactics.
Require Import compiler.SeparationLogic.
Require Import bedrock2.Scalars.

Local Unset Universe Polymorphism.

Section Go.

  Context {W: Words}.
  Context {Registers: map.map Register word}.
  Context {Action: Type}.
  Context {mem: map.map word byte}.
  Context {mem_ok: map.ok mem}.

  Local Notation RiscvMachineL := (RiscvMachine Register Action).

  Context {M: Type -> Type}.
  Context {MM: Monad M}.
  Context {RVM: RiscvProgram M word}.
  Context {RVS: @RiscvState M word _ _ RVM}.
  Context {RVAX: AxiomaticRiscv Action M}.
  Variable iset: InstructionSet.

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

  Require Import riscv.Encode.
  Require Import riscv.proofs.EncodeBound.

  Definition ptsto_instr(addr: word)(instr: Instruction): mem -> Prop :=
    scalar Syntax.access_size.four addr (word.of_Z (encode instr)).

  Definition program(addr: word)(prog: list Instruction): mem -> Prop :=
    array ptsto_instr (word.of_Z 4) addr prog.

  Lemma go_fetch_inst: forall {inst initialL pc0} {R: mem -> Prop} (post: RiscvMachineL -> Prop),
      pc0 = initialL.(getPc) ->
      (program pc0 [inst] * R)%sep initialL.(getMem) ->
      verify inst iset ->
      mcomp_sat (Bind (execute inst) (fun _ => step)) initialL post ->
      mcomp_sat (run1 iset) initialL post.
  Proof.
    intros. subst.
    unfold run1.
    apply go_getPC.
    unfold program, array, ptsto_instr in *.

    eapply go_loadWord.
    unfold Memory.loadWord.

    - eapply load_bytes_sep.
      unfold scalar, littleendian, Memory.bytes_per in H0.
      (* TODO here it would be useful if seplog unfolded Memory.bytes_per for me,
         ie. did more than just syntactic unify *)
      seplog.
    - rewrite combine_split.
      rewrite word.unsigned_of_Z.
      assert (0 <= encode inst < 2 ^ width) as F. {
        pose proof (encode_range inst) as P.
        destruct width_cases as [E | E]; rewrite E; split.
        + Fail lia. omega. (* COQBUG lia doesn't understand universes well enough *)
        + Fail lia. omega.
        + Fail lia. omega.
        + let r := eval cbv in (2 ^ 32) in change (2 ^ 32) with r in *.
          let r := eval cbv in (2 ^ 64) in change (2 ^ 64) with r in *.
          omega.
      }
      do 2 rewrite Z.mod_small; try assumption; try apply encode_range.
      rewrite decode_encode; assumption.
  Qed.

End Go.
