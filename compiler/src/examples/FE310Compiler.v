Require Import Coq.Lists.List.
Require Import coqutil.Z.Lia.
Import ListNotations.
Require Import coqutil.Decidable.
Require Import compiler.ExprImp.
Require Import compiler.NameGen.
Require Import compiler.Pipeline.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Map.SortedList.
Require coqutil.Map.SortedListString.
Require Import coqutil.Word.Naive riscv.Utility.Words32Naive.
Require Import riscv.Utility.DefaultMemImpl32.
Require Import coqutil.Map.Empty_set_keyed_map.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require Import riscv.Utility.Monads.
Require Import compiler.util.Common.
Require        riscv.Utility.InstructionNotations.
Require Import riscv.Platform.MetricLogging.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Platform.MinimalMMIO.
Require Import riscv.Platform.MetricMinimalMMIO.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.Encode.
Require Import coqutil.Map.SortedList.
Require Import compiler.ZNameGen.
Require Import riscv.Utility.InstructionCoercions.
Require Import bedrock2.Byte.
Require bedrock2.Hexdump.
Require Import compiler.examples.MMIO.
Require Import coqutil.Z.HexNotation.
Require Import compiler.GoFlatToRiscv.

Unset Universe Minimization ToSet.

Open Scope Z_scope.


Existing Instance coqutil.Map.SortedListString.map.
Existing Instance coqutil.Map.SortedListString.ok.

Instance mmio_params: MMIO.parameters := { (* everything is inferred automatically *) }.

(* needed because different unfolding levels of implicit arguments *)
Instance riscv_ext_spec': ExtSpec := processor_mmio.
Instance MetricMinimalMMIOPrimitivesParams':
  PrimitivesParams (free action result) MetricRiscvMachine :=
  MetricMinimalMMIOPrimitivesParams.

Instance pipeline_params: Pipeline.parameters := {
  Pipeline.ext_spec := FlatToRiscvCommon.FlatToRiscv.ext_spec;
  Pipeline.ext_guarantee := FlatToRiscvCommon.FlatToRiscv.ext_guarantee;
  Pipeline.PRParams := MetricMinimalMMIOPrimitivesParams;
  Pipeline.RVM := MetricMinimalMMIO.IsRiscvMachine;
}.

Lemma undef_on_same_domain{K V: Type}{M: map.map K V}(keq: K -> K -> bool){keq_spec: EqDecider keq}{Ok: map.ok M}
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
  constructor; try typeclasses eauto; try refine FlatToRiscv_hyps;
    try exact MetricMinimalMMIOSatisfiesPrimitives.
  constructor; unfold ext_spec, pipeline_params; simpl.
  - intros *. intros [? _] [? _]. subst. apply map.same_domain_refl.
  - unfold bedrock2_interact. intros.
    cbv [Morphisms.Proper Morphisms.respectful Basics.impl Morphisms.pointwise_relation]; intros.
    destruct H0; destruct H0. subst.
    split; [reflexivity|].
    repeat (destruct_one_match_hyp; try contradiction).
    all: subst.
    { destruct H1 as (?&?&?&?&?); subst.
      eexists _, _; split; [|split]; eauto. }
    { destruct H1 as (?&?&?&?); subst.
      eexists  _; split; [|split]; eauto. }
  - unfold bedrock2_interact. intros.
    destruct H0; destruct H0.
    split; [reflexivity|].
    repeat (destruct_one_match_hyp; try contradiction).
    all: subst.
    { destruct H1 as (?&?&?&?&?); subst.
      destruct H as (?&?&?&?&?&?); subst.
      eexists _, _; split; [|split]; eauto. }
    { destruct H1 as (?&?&?&?); subst.
      destruct H as (?&?&?&?&?); subst.
      eexists  _; split; [|split]; eauto. }
Qed.

Definition compileFunc: cmd -> list Instruction := ExprImp2Riscv.

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

Definition zeroedRiscvMachine: MetricRiscvMachine := {|
  getMetrics := EmptyMetricLog;
  getMachine := {|
    getRegs := map.empty;
    getPc := word.of_Z 0;
    getNextPc := word.of_Z 4;
    getMem := map.empty;
    getXAddrs := nil;
    getLog := nil;
  |};
|}.

Definition imemStart: word := word.of_Z (Ox "20400000").
Lemma imemStart_div4: word.unsigned imemStart mod 4 = 0. reflexivity. Qed.

Definition initialRiscvMachine(imem: list MachineInt): MetricRiscvMachine :=
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

Definition initialSwapMachine: MetricRiscvMachine :=
  initialRiscvMachine (List.map encode (compileFunc swap_chars_over_uart)).

(* just to make sure all typeclass instances are available: *)
Definition mcomp_sat:
  free action result unit -> MetricRiscvMachine -> (MetricRiscvMachine -> Prop) -> Prop :=
  GoFlatToRiscv.mcomp_sat (PRParams := MetricMinimalMMIOPrimitivesParams).

Lemma undef_on_unchecked_store_byte_list:
  forall (l: list word8) (start: word32),
    map.undef_on (unchecked_store_byte_list start l map.empty)
                 (fun x =>
                    start <> x /\
                    word.unsigned (word.sub start x) + Z.of_nat (List.length l) < 2 ^ width).
Proof.
  unfold map.undef_on, map.agree_on. intros. rewrite map.get_empty.
  unfold PropSet.elem_of in *.
  pose proof putmany_of_footprint_None' as P.
  unfold unchecked_store_byte_list, unchecked_store_bytes.
  apply P; clear P; intuition idtac.
Qed.

Lemma map_undef_on_weaken{K V: Type}(keq: K -> K -> bool){keq_spec: EqDecider keq}{M: map.map K V}{Ok: map.ok M}:
  forall (P Q: PropSet.set K) (m: M),
    map.undef_on m Q ->
    PropSet.subset P Q ->
    map.undef_on m P.
Proof.
  intros. map_solver Ok.
Qed.

Lemma initialMachine_undef_on_MMIO_addresses: map.undef_on (getMem initialSwapMachine) isMMIOAddr.
Proof.
  cbv [getMem initialSwapMachine initialRiscvMachine putProgram].
  cbv [withPc withNextPc withMem getMem zeroedRiscvMachine].
  eapply map_undef_on_weaken with (keq := word.eqb); try typeclasses eauto.
  - apply undef_on_unchecked_store_byte_list.
  - unfold PropSet.subset, PropSet.elem_of.
    intros addr El. unfold isMMIOAddr in El. destruct El as [El1 El2].
    cbv [isOTP isPRCI isGPIO0 isUART0] in *.
    split.
    + intro C. rewrite <- C in *. unfold imemStart in *. cbv in El2. intuition congruence.
    + rewrite word.unsigned_sub.
      unfold imemStart. rewrite word.unsigned_of_Z. unfold word.wrap. rewrite Zminus_mod_idemp_l.
      match goal with
      | |- _ + ?L < ?M => let L' := eval cbv in L in change L with L';
                          let M' := eval cbv in M in change M with M'
      end.
      match type of El2 with
      | _ <= ?a < _ \/ _ => remember a as addr'
      end.
      match goal with
      | |- (_ - ?a) mod _ + _ < _ => replace a with addr'
      end.
      hex_csts_to_dec.
      rewrite Z.mod_small; blia.
Qed.

