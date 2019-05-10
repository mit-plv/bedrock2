Require Import String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.

Require Import Kami.
Require Import Kami.Ex.SC Kami.Ex.IsaRv32 Kami.Ex.SCMMInl.
Require Import Kami.Ex.ProcMemCorrect.

Local Open Scope Z_scope.

Definition width: Z := 32.
Definition width_cases: width = 32 \/ width = 64 := or_introl eq_refl.
Local Notation nwidth := (Z.to_nat width).

Definition isMMIO: IsMMIOT nwidth :=
  (fun _ addr => ($$false)%kami_expr).

Section PerInstAddr.
  Context {instrMemSizeLg: Z}.
  Local Notation ninstrMemSizeLg := (Z.to_nat instrMemSizeLg).

  Definition procInit: ProcInit ninstrMemSizeLg rv32DataBytes rv32RfIdx :=
    {| pcInit := getDefaultConst _;
       rfInit := getDefaultConst _ |}.

  Definition predictNextPc ty (ppc: fullType ty (SyntaxKind (Pc ninstrMemSizeLg))) :=
    (#ppc + $4)%kami_expr.

  Definition scmmInl :=
    @scmmInl
      nwidth ninstrMemSizeLg
      rv32InstBytes rv32DataBytes rv32RfIdx rv32GetOptype
      rv32GetLdDst (rv32GetLdAddr _) rv32GetLdSrc (rv32CalcLdAddr _)
      (rv32GetStAddr _) rv32GetStSrc (rv32CalcStAddr _) rv32GetStVSrc
      rv32GetSrc1 rv32GetSrc2 rv32GetDst (rv32Exec _)
      (rv32NextPc _) (rv32AlignAddr _)
      isMMIO procInit.

  Definition proc: Kami.Syntax.Modules := projT1 scmmInl.

  Definition hst := Kami.Semantics.RegsT.

  (** Abstract hardware state *)
  Record st :=
    mk { pc: word (2 + ninstrMemSizeLg);
         rf: word rv32RfIdx -> word nwidth;
         pgm: word ninstrMemSizeLg -> word nwidth;
         mem: word nwidth -> word nwidth
       }.

  Definition RegsToT (r: hst): option st :=
    (mlet pinit: Bool <- r |> "pinit" <| None;
       if pinit
       then (mlet pcv: (Pc ninstrMemSizeLg) <- r |> "pc" <| None;
               mlet rfv: (Vector (Bit nwidth) rv32RfIdx) <- r |> "rf" <| None;
               mlet pgmv: (Vector (Bit nwidth) ninstrMemSizeLg) <- r |> "pgm" <| None;
               mlet memv: (Vector (Bit nwidth) nwidth) <- r |> "mem" <| None;
               (Some {| pc := pcv;
                        rf := rfv;
                        pgm := pgmv;
                        mem := memv |}))
       else None)%mapping.

  (** Refinement from [p4mm] to [proc] (as a spec) *)

  Definition p4mm: Kami.Syntax.Modules :=
    p4mm 1 rv32GetOptype
         rv32GetLdDst (rv32GetLdAddr _) rv32GetLdSrc (rv32CalcLdAddr _)
         (rv32GetStAddr _) rv32GetStSrc (rv32CalcStAddr _) rv32GetStVSrc
         rv32GetSrc1 rv32GetSrc2 rv32GetDst (rv32Exec _)
         (rv32NextPc _) (rv32AlignAddr _)
         predictNextPc isMMIO procInit.

  Theorem proc_correct: p4mm <<== proc.
  Proof.
    ketrans.
    - apply p4mm_correct. (* [p4mm] refines [scmm] *)
    - apply (projT2 scmmInl). (* [scmm] refines [projT1 scmmInl], the inlined module. *)
  Qed.

End PerInstAddr.
