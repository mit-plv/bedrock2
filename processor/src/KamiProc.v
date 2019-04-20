Require Import String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.

Require Import Kami.
Require Import Kami.Ex.SC Kami.Ex.IsaRv32 Kami.Ex.SCMMInl.

Local Open Scope Z_scope.

Definition width: Z := 32.
Definition width_cases: width = 32 \/ width = 64 := or_introl eq_refl.
Definition nwidth := Z.to_nat width.

Definition procInit: ProcInit nwidth rv32DataBytes rv32RfIdx :=
  {| pcInit := getDefaultConst _;
     rfInit := getDefaultConst _ |}.

Local Definition addrSize := nwidth.

Definition isMMIO: IsMMIOT nwidth :=
  (fun _ addr => ($$false)%kami_expr).

Section PerInstAddr.

  Context {instrMemSizeLg: Z}.

  Local Definition ninstrMemSizeLg := Z.to_nat instrMemSizeLg.

  Definition proc: Kami.Syntax.Modules :=
    projT1 (@scmmInl
              nwidth ninstrMemSizeLg
              rv32InstBytes rv32DataBytes rv32RfIdx rv32GetOptype
              rv32GetLdDst (rv32GetLdAddr _) rv32GetLdSrc (rv32CalcLdAddr _)
              (rv32GetStAddr _) rv32GetStSrc (rv32CalcStAddr _) rv32GetStVSrc
              rv32GetSrc1 rv32GetSrc2 rv32GetDst (rv32Exec _)
              (rv32NextPc _) (rv32AlignPc _ _) (rv32AlignAddr _)
              isMMIO procInit).

  Definition hst := Kami.Semantics.RegsT.

  (** Abstract hardware state *)
  Record st :=
    mk { pc: word nwidth;
         rf: word rv32RfIdx -> word nwidth;
         pgm: word ninstrMemSizeLg -> word nwidth;
         mem: word nwidth -> word nwidth
       }.

  Definition RegsToT (r: hst): option st :=
    (mlet pinit: Bool <- r |> "pinit" <| None;
       if pinit
       then (mlet pcv: (Bit nwidth) <- r |> "pc" <| None;
               mlet rfv: (Vector (Bit nwidth) rv32RfIdx) <- r |> "rf" <| None;
               mlet pgmv: (Vector (Bit nwidth) ninstrMemSizeLg) <- r |> "pgm" <| None;
               mlet memv: (Vector (Bit nwidth) nwidth) <- r |> "mem" <| None;
               (Some {| pc := pcv;
                        rf := rfv;
                        pgm := pgmv;
                        mem := memv |}))
       else None)%mapping.

End PerInstAddr.

