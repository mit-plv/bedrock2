Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Require Import coqutil.Decidable.
Require Import compiler.ExprImp.
Require Import compiler.NameGen.
Require Import compiler.Pipeline.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Map.SortedList.
Require Import riscv.Utility.Words32Naive.
Require Import riscv.Utility.DefaultMemImpl32.
Require Import coqutil.Map.Empty_set_keyed_map.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require Import riscv.Utility.Monads.
Require Import compiler.util.Common.
Require        riscv.Utility.InstructionNotations.
Require Import riscv.Platform.MinimalMMIO.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.Encode.
Require Import coqutil.Map.SortedList.
Require Import compiler.ZNameGen.
Require Import riscv.Utility.InstructionCoercions.
Require Import bedrock2.Byte.
Require bedrock2.Hexdump.
Require Import compiler.examples.MMIO.
Require Import coqutil.Z.HexNotation.

Unset Universe Minimization ToSet.

Open Scope Z_scope.

Notation RiscvMachine := (RiscvMachine Register MMIOAction).

Instance mmio_params: MMIO.parameters := { (* everything is inferred automatically *) }.

Existing Instance MinimalMMIOPrimitivesParams. (* needed because it's in a section *)

Instance pipeline_params: Pipeline.parameters := {
  Pipeline.ext_spec := FlatToRiscv.FlatToRiscv.ext_spec;
  Pipeline.ext_guarantee := FlatToRiscv.FlatToRiscv.ext_guarantee;
  Pipeline.M := OStateND RiscvMachine;
  Pipeline.PRParams := MinimalMMIOPrimitivesParams;
}.

Instance word32eqdec: DecidableEq word32. Admitted.

Lemma undef_on_same_domain{K V: Type}{M: map.map K V}{keq: DecidableEq K}{Ok: map.ok M}
      (m1 m2: M)(P: K -> Prop):
  map.undef_on m1 P ->
  map.same_domain m1 m2 ->
  map.undef_on m2 P.
Proof.
  intros. unfold map.same_domain, map.sub_domain in *.
  Fail solve [map_solver Ok]. (* TODO map_solver make this work (without separate lemma) *)
  repeat autounfold with unf_map_defs in *.
  intros k Pk.
  rewrite map.get_empty.
  destruct (map.get m2 k) eqn: E; [exfalso|reflexivity].
  destruct H0 as [_ A].
  specialize A with (1 := E).
  destruct A as [v2 A].
  specialize (H k Pk).
  rewrite map.get_empty in H.
  congruence.
Qed.

Instance pipeline_assumptions: @Pipeline.assumptions pipeline_params.
Proof.
  constructor; try typeclasses eauto.
  constructor; unfold ext_spec, pipeline_params; simpl.
  - intros *. intros [? _] [? _]. subst. apply map.same_domain_refl.
  - unfold real_ext_spec. intros.
    destruct H; destruct H0. subst.
    split; [reflexivity|].
    repeat (destruct_one_match_hyp; try contradiction).
    all: intuition eauto.
Qed.

Definition compileFunc: cmd -> list Instruction := exprImp2Riscv.

Definition instructions_to_word8(insts: list Instruction): list Utility.byte :=
  List.flat_map (fun inst => HList.tuple.to_list (LittleEndian.split 4 (encode inst))) insts.

Definition main(c: cmd): list byte :=
  let instrs := compileFunc c in
  let word8s := instructions_to_word8 instrs in
  List.map (fun w => Byte.of_Z (word.unsigned w)) word8s.

(*
   a = input(magicMMIOAddrLit);
   b = input(magicMMIOAddrLit);
   output(magicMMIOAddrLit, a+b);
*)
Example a: varname := 1.
Example b: varname := 2.
Example mmio_adder: cmd :=
  (cmd.seq (cmd.interact [a] MMInput [expr.literal magicMMIOAddrLit])
  (cmd.seq (cmd.interact [b] MMInput [expr.literal magicMMIOAddrLit])
           (cmd.interact [] MMOutput [expr.literal magicMMIOAddrLit;
                                        expr.op bopname.add (expr.var a) (expr.var b)]))).

(* Eval vm_compute in compileFunc mmio_adder. *)

Definition mmio_adder_bytes: list byte := Eval vm_compute in main mmio_adder.


Require Import bedrock2.Examples.FE310CompilerDemo.
Time Definition swap_demo_byte: list byte := Eval vm_compute in main swap_chars_over_uart.

Module PrintAssembly.
  Import riscv.Utility.InstructionNotations.
  (* Eval vm_compute in compileFunc swap_chars_over_uart. *)
End PrintAssembly.

Definition zeroedRiscvMachine: RiscvMachine := {|
  getRegs := map.empty;
  getPc := word.of_Z 0;
  getNextPc := word.of_Z 4;
  getMem := map.empty;
  getLog := nil;
|}.

Definition imemStart: word := word.of_Z (Ox "20400000").
Lemma imemStart_div4: word.unsigned imemStart mod 4 = 0. reflexivity. Qed.

Definition initialRiscvMachine(imem: list MachineInt): RiscvMachine :=
  putProgram imem imemStart zeroedRiscvMachine.

Require bedrock2.WeakestPreconditionProperties.

Local Instance ext_spec_Proper :   forall
    (trace : list
               (mem * actname * list Semantics.word *
                (mem * list Semantics.word))) (m : mem)
    (act : actname) (args : list Semantics.word),
  Morphisms.Proper
    (Morphisms.respectful
       (Morphisms.pointwise_relation mem
          (Morphisms.pointwise_relation (list Semantics.word) Basics.impl))
       Basics.impl) (ext_spec trace m act args).
Admitted.

Definition initialSwapMachine: RiscvMachine :=
  initialRiscvMachine (List.map encode (compileFunc swap_chars_over_uart)).

(* just to make sure all typeclass instances are available: *)
Definition mcomp_sat:
  OStateND RiscvMachine unit -> RiscvMachine -> (RiscvMachine -> Prop) -> Prop :=
  GoFlatToRiscv.mcomp_sat.

Definition unchecked_store_program(addr: word)(p: list Instruction)(m: mem): mem :=
  unchecked_store_byte_tuple_list addr (List.map (LittleEndian.split 4) (List.map encode p)) m.

Lemma store_program_empty: forall prog addr,
    GoFlatToRiscv.program addr prog (unchecked_store_program addr prog map.empty).
Proof.
  induction prog; intros.
  - cbv. auto.
  - cbv [GoFlatToRiscv.program]. simpl.
    do 2 eexists. split; [|split].
Admitted.

Lemma undef_on_unchecked_store_byte_tuple_list:
  forall (n: nat) (l: list (HList.tuple word8 n)) (start: word32),
    map.undef_on (unchecked_store_byte_tuple_list start l map.empty)
                 (fun x => ~ word.unsigned start <=
                           word.unsigned x <
                           word.unsigned start + Z.of_nat n * Zlength l).
Proof.
  induction l; intros.
  - admit.
  - rewrite unchecked_store_byte_tuple_list_cons.
Admitted.

Lemma map_undef_on_weaken: forall (P Q: PropSet.set word32) (m: Mem),
    map.undef_on m Q ->
    PropSet.subset P Q ->
    map.undef_on m P.
Admitted.

Lemma initialMachine_undef_on_MMIO_addresses: map.undef_on (getMem initialSwapMachine) isMMIOAddr.
Proof.
  cbv [getMem initialSwapMachine initialRiscvMachine putProgram].
  cbv [withPc withNextPc withMem getMem zeroedRiscvMachine].
  eapply map_undef_on_weaken.
  - apply undef_on_unchecked_store_byte_tuple_list.
  - unfold PropSet.subset, PropSet.elem_of.
    intros addr El C. unfold isMMIOAddr in El. destruct El as [El1 El2].
    match type of C with
    | ?x <= _ < ?y => let y' := eval cbv in y in change y with y' in C;
                      let x' := eval cbv in x in change x with x' in C
    end.
    cbv [isGPIO0 isQSPI1] in *.
    repeat match goal with
           | _: context [Ox ?s] |- _ => let r := eval cbv in (Ox s) in change (Ox s) with r in *
           end.
    simpl in *.
    lia.
Qed.

Lemma input_program_correct:
  exec map.empty swap_chars_over_uart [] map.empty map.empty (fun t m l => True).
Proof.
  eapply bedrock2.WeakestPreconditionProperties.sound_nil.
  eapply bedrock2.Examples.FE310CompilerDemo.swap_chars_over_uart_correct.
Qed.
Print Assumptions input_program_correct. (* some axioms *)

Lemma end2endDemo:
  runsToNonDet.runsTo (mcomp_sat (run1 RV32IM))
                      initialSwapMachine
                      (fun (finalL: RiscvMachine) =>  (fun _ => True) finalL.(getLog)).
Proof.
  refine (@exprImp2Riscv_correct _ _ swap_chars_over_uart map.empty nil _ _ _ _ _ _ _ _ _ _ _ _).
  - reflexivity.
  - cbv. repeat constructor.
  - reflexivity.
  - exact imemStart_div4.
  - reflexivity.
  - reflexivity.
  - cbv [initialSwapMachine initialRiscvMachine getMem putProgram zeroedRiscvMachine
         getMem withPc withNextPc withMem].
    unfold Separation.sep. do 2 eexists; split; [ | split; [|reflexivity] ].
    1: apply map.split_empty_r; reflexivity.
    apply store_program_empty.
  - cbv [Pipeline.ext_guarantee pipeline_params FlatToRiscv.FlatToRiscv.ext_guarantee
         FlatToRiscv_params mmio_params].
    exact initialMachine_undef_on_MMIO_addresses.
  - apply input_program_correct.
Qed.
Print Assumptions end2endDemo. (* many axioms *)
