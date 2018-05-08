Require Import Coq.Lists.List.
Import ListNotations.
Require Import lib.LibTacticsMin.
Require Import bbv.Word.
Require Import compiler.Decidable.
Require Import compiler.Op.
Require Import compiler.ExprImp.
Require Import compiler.NameGen.
Require Import compiler.Common.
Require Import compiler.Pipeline.
Require Import riscv.Riscv.
Require Import compiler.MyOmega.
Require Import riscv.util.Monads.
Require Import compiler.NameWithEq.
Require Import riscv.RiscvBitWidths.
Require Import riscv.InstructionCoercions.
Require Import riscv.ListMemory.
Require Import riscv.MinimalLogging.
Require Import riscv.Utility.
Require Import riscv.encode.Encode.

Require Import riscv.RiscvBitWidths32.

Open Scope Z_scope.

Definition var: Set := (@name FlatImp.TestFlatImp.ZName).
Definition Reg: Set := (@name FlatImp.TestFlatImp.ZName).

Existing Instance DefaultRiscvState.

Instance FunctionRegisterFile: RegisterFile (Register -> word wXLEN) Register (word wXLEN) := {|
  getReg(rf: Register -> word wXLEN) := rf;
  setReg(rf: Register -> word wXLEN)(r: Register)(v: word wXLEN) :=
    fun r' => if (Z.eqb r' r) then v else rf r';
  initialRegs := fun r => $0;
|}.

Definition var_a: var := 1.
Definition var_b: var := 2.
Definition var_c: var := 3.
Definition var_i: var := 4.

(*
a = 0
b = 1
i = 0
while i < n:
  c = a + b
  a = b
  b = c
  i = i + 1
*)

Definition fib_ExprImp(n: word wXLEN): stmt :=
  SSeq (SSet var_a (ELit $0)) (
  SSeq (SSet var_b (ELit $1)) (
  SSeq (SSet var_i (ELit $0)) (
  SWhile (EOp OLt (EVar var_i) (ELit n)) (
    SSeq (SSet var_c (EOp OPlus (EVar var_a) (EVar var_b))) (
    SSeq (SSet var_a (EVar var_b)) (
    SSeq (SSet var_b (EVar var_c)) (
    SSeq (SSet var_i (EOp OPlus (EVar var_i) (ELit $1)))
    SSkip))))))).

Definition state := (var -> option (word wXLEN)).

Definition fib_H_res(fuel: nat)(n: word wXLEN): option (word wXLEN) :=
  match (eval_stmt fuel empty Memory.no_mem (fib_ExprImp n)) with
  | Some (st, m) => st var_b
  | None => None
  end.


Goal fib_H_res 20 $0 = Some $1. reflexivity. Qed.
Goal fib_H_res 20 $1 = Some $1. reflexivity. Qed.
Goal fib_H_res 20 $2 = Some $2. reflexivity. Qed.
Goal fib_H_res 20 $3 = Some $3. reflexivity. Qed.
Goal fib_H_res 20 $4 = Some $5. reflexivity. Qed.
Goal fib_H_res 20 $5 = Some $8. reflexivity. Qed.
Goal fib_H_res 20 $6 = Some $13. reflexivity. Qed.


(* exprImp2Riscv is the main compilation function *)
Definition fib_riscv0(n: word wXLEN): list Instruction :=
  exprImp2Riscv (fib_ExprImp n).

Notation "'RISCV' {{ x ; y ; .. ; z }}" := (@cons Instruction x
  (@cons Instruction y .. (@cons Instruction z nil) ..))
  (format "'RISCV' {{ '[v' '//' x ; '//' y ; '//' .. ; '//' z ']' '//' }}").

Definition fib6_riscv': list Instruction := ltac:(
  let fl := constr:(let (sFlat, _) :=
         FlattenExpr.flattenStmt (freshNameGenState (allVars_stmt (fib_ExprImp $ (6))))
           (fib_ExprImp $ (6)) in
             sFlat) in
  let fl := eval simpl in fl in
  let r := constr:(FlatToRiscv.compile_stmt fl) in
  let r := eval simpl in r in
  exact r).

Print fib6_riscv'.

Ltac simpl_wordToZ r :=
      match r with
      | context C[wordToZ ?x] =>
        let s := eval cbv in (wordToZ x) in
            let r' := context C[s] in
            simpl_wordToZ r'
      | _ => r
      end.

Definition fib6_riscv: list Instruction := ltac:(
  let r := eval unfold fib6_riscv' in fib6_riscv' in
  let t := simpl_wordToZ r in
  exact t).

Print fib6_riscv.

Definition fib6_bits: list (word 32) :=
  ltac:(let res := eval cbv in (map (fun i => ZToWord 32 (encode i)) fib6_riscv) in exact res).

Print fib6_bits.

(* This example uses the memory only as instruction memory
   TODO make an example which uses memory to store data *)
Definition zeroedRiscvMachineCore: RiscvMachineCore := {|
  registers := initialRegs;
  pc := $0;
  nextPC := $4;
  exceptionHandlerAddr := 3;
|}.

Definition zeroedRiscvMachine: RiscvMachine := {|
    core := zeroedRiscvMachineCore;
    machineMem := zero_mem ((length fib6_riscv) * 4);
|}.

Definition zeroedRiscvMachineL: RiscvMachineL := {|
    machine := zeroedRiscvMachine;
    log := nil;
|}.

Definition initialRiscvMachine(imem: list (word 32)): RiscvMachineL :=
  putProgram imem zeroedRiscvMachineL.

Definition run: nat -> RiscvMachineL -> option unit * RiscvMachineL :=
 @run RiscvBitWidths32 MachineWidth32 (OState RiscvMachineL) (OState_Monad _) _ _  .

Definition fib6_L_final(fuel: nat): RiscvMachineL :=
  snd (run fuel (initialRiscvMachine fib6_bits)).

Definition fib6_L_res(fuel: nat): word wXLEN :=
  (fib6_L_final fuel).(machine).(core).(registers) var_b.

Definition fib6_L_trace(fuel: nat): Log :=
  (fib6_L_final fuel).(log).

(* only uncomment this if you're sure there are no admits in the computational parts,
   and that no computations match on opaque proofs,
   otherwise this will eat all your memory *)

Eval cbv in (fib6_L_trace 1000).
Eval cbv in (length (fib6_L_trace 1000)).

Eval cbv in (fib6_L_res 200).

(* If cbv and vm_compute block or better performance is needed, we can extract to Haskell: *)
Definition finalfibres: nat := wordToNat (fib6_L_res 200).
Require Extraction.
Extraction Language Haskell.
Set Warnings "-extraction-reserved-identifier".
Extraction "Fib6.hs" finalfibres.


(* 1st method: Run it *)
Lemma fib6_L_res_is_13_by_running_it: exists fuel, fib6_L_res fuel = $13.
  exists 200%nat.
  cbv.
  reflexivity.
Qed.

(* 2nd method: Prove it without running it, but using the compiler correctness theorem *)
Lemma fib6_L_res_is_13_by_proving_it: exists fuel, fib6_L_res fuel = $13.
  unfold fib6_L_res. unfold fib6_L_final.
  pose proof @exprImp2Riscv_correct as P.
  (* TODO first finish updating compiler correctness theorem
  assert (exists finalH, evalH 20 empty (fib_ExprImp $ (6)) = Some finalH) as F. {
    eexists. reflexivity.
  }
  destruct F as [finalH F].
  specialize P with (3 := F).
  specialize P with (varset := Function_Set var) (NG := NatNameGen).
  specialize (P (initialRiscvMachine fib6_riscv)).
  edestruct P as [fuelL G].
  - cbv. omega.
  - reflexivity.
  - exists fuelL. apply G.
    assert (forall T (a b: T), Some a = Some b -> a = b) as E. {
      introv R. inversion R. reflexivity.
    }
    apply E in F.
    rewrite <- F. clear F.
    cbv. reflexivity.
  *)
Admitted.
