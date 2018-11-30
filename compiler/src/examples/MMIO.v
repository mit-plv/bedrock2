Require Import Coq.ZArith.ZArith.
Require Import riscv.util.Word.
Require Import riscv.util.BitWidths.
Require Import compiler.util.Common.
Require Import compiler.Op.
Require Import riscv.util.BitWidth32.
Require Import riscv.util.Monads.
Require Import compiler.util.List_Map.
Require Import compiler.util.List_Set.
Require Import compiler.FlatImp.
Require Import riscv.MachineWidth32.
Require Import riscv.util.ListLib.
Require Import riscv.Decode.
Require Import riscv.Utility.
Require Import riscv.PseudoInstructions.
Require Import riscv.InstructionCoercions.
Require Import riscv.Program.
Require Import compiler.FlatToRiscvDef.
Require Import compiler.FlatToRiscv.
Require Import riscv.ListMemory.
Require Import compiler.FlatToRiscv32Proofs.
Require Import compiler.FlatToRiscv32Specifics.
Require Import riscv.RiscvMachine.
Require Import riscv.MinimalMMIO.
Require Import compiler.FlatToRiscvDef.
Require Import riscv.AxiomaticRiscv.
Require Import compiler.runsToNonDet.
Require Import compiler.containsProgram.
Import ListNotations.
Existing Instance DefaultRiscvState.

Open Scope ilist_scope.

Definition var: Set := Z.
Definition func: Set := Empty_set.

Instance act_dec: DecidableEq MMIOAction.
intros a b. destruct a; destruct b; (left + right); congruence.
Defined.

Instance myparams: Basic_bopnames.parameters := {|
  varname := var;
  funcname := func;
  actname := MMIOAction;
|}.

Instance annoying: DecidableEq (list varname * list varname * stmt). Admitted.

Definition trace := list (LogItem (word 32) actname).

Module HardToRead.

  Inductive ext_spec: MMIOAction -> trace -> list (word 32) ->
                      (trace -> list (word 32) -> Prop) -> Prop :=
  | ext_input: forall t addr,
      simple_isMMIOAddr addr = true ->
      ext_spec MMInput t [addr]
               (* note: no restrictions on val: that's the source of non-determinism *)
               (fun t' results => exists val, t' = (MMInput, [addr], [val]) :: t /\ results = [val])
  | ext_output: forall t addr val,
      simple_isMMIOAddr addr = true ->
      ext_spec MMOutput t [addr; val]
               (fun t' results => t' = (MMOutput, [addr; val], nil) :: t /\ results = nil).

End HardToRead.

Module Wrong.

  Inductive ext_spec: MMIOAction -> trace -> list (word 32) ->
                      (trace -> list (word 32) -> Prop) -> Prop :=
  | ext_input: forall t addr val,
      (* note: val is quantified in the wrong place *)
      simple_isMMIOAddr addr = true ->
      ext_spec MMInput t [addr]
               (fun t' results => t' = (MMInput, [addr], [val]) :: t /\ results = [val])
  | ext_output: forall t addr val,
      simple_isMMIOAddr addr = true ->
      ext_spec MMOutput t [addr; val]
               (fun t' results => t' = (MMOutput, [addr; val], nil) :: t /\ results = nil).

End Wrong.

Definition ext_spec(a: MMIOAction)(t: trace)(argvals: list (word 32))
                   (outcome: trace -> list (word 32) -> Prop): Prop :=
  match a with
  | MMInput =>
    exists addr, argvals = [addr] /\
                 simple_isMMIOAddr addr = true /\
                 forall t' resvals, outcome t' resvals ->
                                    exists val, t' = (MMInput, [addr], [val]) :: t /\
                                                resvals = [val]
  | MMOutput =>
    exists addr val, argvals = [addr; val] /\
                     simple_isMMIOAddr addr = true /\
                     forall t' resvals, outcome t' resvals ->
                                        t' = (MMOutput, [addr; val], nil) :: t /\ resvals = nil
  end.

Lemma hardToRead_implies_ext_spec: forall a t argvals outcome,
    HardToRead.ext_spec a t argvals outcome ->
    ext_spec a t argvals outcome.
Proof.
  intros. inversion H; subst; clear H; simpl in *; eauto.
Qed.

Lemma ext_spec_implies_hardToRead: forall a t argvals outcome,
    ext_spec a t argvals outcome ->
    exists (preciseOutcome: _ -> _ -> Prop),
      (forall t' resvals, preciseOutcome t' resvals -> outcome t' resvals) /\
      HardToRead.ext_spec a t argvals preciseOutcome.
Proof.
(* not sure if it holds, because preciseOutcome needs to syntactically match,
   but also needs to imply outcome *)
Abort.

Instance myFlatImpParams: FlatImp.parameters := {|
  FlatImp.bopname_params := myparams;
  FlatImp.ext_spec := ext_spec;
|}.

Definition compile_ext_call(results: list var)(a: MMIOAction)(args: list var):
  list Instruction :=
  match a with
  | MMInput =>
    match results, args with
    | [res], [addr] => [[ Lw res addr 0 ]]
    | _, _ => [[]] (* invalid, excluded by ext_spec *)
    end
  | MMOutput =>
    match results, args with
    | [], [addr; val] => [[ Sw addr val 0 ]]
    | _, _ => [[]] (* invalid, excluded by ext_spec *)
    end
  end.

Instance compilation_params: FlatToRiscvDef.parameters := {|
  FlatToRiscvDef.actname := MMIOAction;
  FlatToRiscvDef.LwXLEN := Lw;
  FlatToRiscvDef.SwXLEN := Sw;
  FlatToRiscvDef.compile_ext_call := compile_ext_call;
  FlatToRiscvDef.max_ext_call_code_size := 1;
|}. abstract omega. Defined.

(*
Lemma compile_ext_call_correct: forall initialL action outcome newPc insts
    (argvars resvars: list Register),
  insts = FlatToRiscvDef.compile_ext_call resvars action argvars ->
  newPc = add (getPc initialL) (ZToReg (4 * Zlength insts)) ->
  Forall valid_register argvars ->
  Forall valid_register resvars ->
  containsProgram.containsProgram (getMem initialL) insts (getPc initialL) ->
  ext_spec action (getLog initialL) (List.map (getReg (getRegs initialL)) argvars) outcome ->
  runsTo (RiscvMachine Register (word 32) (MMIOEvent (word 32))) (mcomp_sat Run.run1) initialL
         (fun finalL =>
            forall newLog resvals, outcome newLog resvals ->
              putmany resvars resvals (getRegs initialL) = Some finalL.(getRegs) /\
              finalL.(getPc) = newPc /\
              finalL.(getNextPc) = add newPc (ZToReg 4) /\
              finalL.(getMem) = getMem initialL /\
              finalL.(getLog) = newLog).

            postH
  (forall (newLog : list (MMIOEvent (word 32))) (resvals : list (word 32)),
   outcome newLog resvals ->
   exists newRegs : map Register (word 32),
     putmany resvars resvals (getRegs initialL) = Some newRegs /\
     runsTo (RiscvMachine Register (word 32) (MMIOEvent (word 32)))
       (mcomp_sat Run.run1)
       {|
       getRegs := newRegs;
       getPc := newPc;
       getNextPc := add newPc (ZToReg 4);
       getMem := getMem initialL;
       getLog := newLog |} post) ->
*)

Definition magicMMIOAddrLit: Z := 65524.

(*
addr = magicMMIOAddr;
loop {
  i = input addr;
  stay in loop only if i is non-zero;
  s = i * i;
  output addr s;
}
*)

Definition _addr: varname := 1.
Definition _i: varname := 2.
Definition _s: varname := 3.

Definition squarer: stmt :=
  (SSeq (SLit _addr magicMMIOAddrLit)
        (SLoop (SLoad _i _addr)
               _i
               (SSeq (SOp _s bopname.mul _i _i)
                     (SStore _addr _s)))).

Definition compiled: list Instruction := Eval cbv in compile_stmt squarer.

Print compiled.

Section TODODontDuplicate.

  Let RiscvMachineL := RiscvMachine Register (word 32) MMIOAction.

  Lemma go_fetch_inst: forall {inst initialL pc0} (post: RiscvMachineL -> Prop),
      pc0 = initialL.(getPc) ->
      containsProgram initialL.(getMem) [[inst]] pc0 ->
      mcomp_sat (Bind (Execute.execute inst) (fun (u: unit) => step)) initialL post ->
      mcomp_sat Run.run1 initialL post.
  Proof.
    intros. subst *.
    unfold run1. unfold Run.run1.
    apply go_getPC.
    apply go_loadWord.
    unfold containsProgram in H0. apply proj2 in H0.
    specialize (H0 0 _ eq_refl). subst inst.
    unfold ldInst in *.
    (*
    match type of H1 with
    | context[?x] => progress (ring_simplify x in H1)
    end.
    exact H1.
    *)
  Admitted.

End TODODontDuplicate.

Instance FlatToRiscv_params: FlatToRiscv.parameters := {|
  FlatToRiscv.def_params := compilation_params;
  FlatToRiscv.mword := word 32;
  FlatToRiscv.MachineWidth_Inst := MachineWidth32;
  FlatToRiscv.varMap_Inst := List_Map _ _;
  FlatToRiscv.Memory_Inst := mem_is_Memory (word 32);
  FlatToRiscv.BWS := _;
  FlatToRiscv.BWSP := _;
  FlatToRiscv.M := OStateND (RiscvMachine Register (word 32) MMIOAction);
  FlatToRiscv.MM := OStateND_Monad _;
  FlatToRiscv.RVM := IsRiscvMachineL;
  FlatToRiscv.RVS := DefaultRiscvState;
  FlatToRiscv.RVAX := MinimalMMIOSatisfiesAxioms;
  FlatToRiscv.ext_spec := ext_spec;
|}.
- intros. simpl. unfold default_translate.
  rewrite remu_def.
  rewrite Z.rem_mod_nonneg.
  + change (regToZ_unsigned (ZToWord 32 4)) with 4. rewrite H. reflexivity.
  + pose proof (regToZ_unsigned_bounds a). omega.
  + reflexivity.
- intros. simpl. unfold default_translate.
  rewrite remu_def.
  rewrite Z.rem_mod_nonneg.
  + change (regToZ_unsigned (ZToWord 32 8)) with 8. rewrite H. reflexivity.
  + pose proof (regToZ_unsigned_bounds a). omega.
  + reflexivity.
- intros. simpl. unfold compile_ext_call.
  repeat destruct_one_match; rewrite? Zlength_cons; rewrite? Zlength_nil; cbv; congruence.
- intros.
  destruct initialL as [initialRegs initialPc initialNpc initialIsMem initialMem initialLog].
  cbv [getRegs getPc getNextPc isMem getMem getLog] in *.
  destruct action; simpl in H4.
  + destruct H4 as (addr & E & ? & P).
    do 2 (destruct argvars; simpl in E; try discriminate).
    inversion E. clear E.
    simpl in H.
    (* want to know that resvars is singleton list: should we make compile_ext_call a partial
       function? *)

    (* if we just
    "eapply runsToNonDet.runsToStep.", we will infer a midset which does not include outcome *)
    refine (runsToNonDet.runsToStep _ _ _ _ (fun mid =>
       exists val,
         outcome ((MMInput, [addr], [val]) :: initialLog) [val] /\
         mid = mkRiscvMachine
                 (setReg initialRegs _ val)
                 (add initialPc (ZToReg 4))
                 (add initialNpc (ZToReg 4))
                 initialIsMem
                 initialMem
                 ((MMInput, [addr], [val]) :: initialLog)) _ _).
    * eapply go_fetch_inst; [reflexivity|..].
simpl. eassumption.
      apply go_getPC.
      apply go_loadWord.

      (* needs go_ or do_ lemmas *)
      admit.
    * intros.
      destruct H6 as (val & ? & ?).
      specialize H5 with (1 := H6). destruct H5 as (newRegs & ? & H5).
      rewrite H8.
      match goal with
      | H: runsTo _ _ ?m1 post |- runsTo _ _ ?m2 post => replace m2 with m1; [apply H|]
      end.
      f_equal.
      -- clear H5.
         do 2 (destruct resvars; simpl in H9; try discriminate).
         apply invert_Some_eq_Some in H9. subst newRegs.
         (* we only get the register too late!
            possible fixes:
            - add typechecking for external calls (redundant?)
            - rephrase ext_call_correct without "CPS" style, but with "call post" style
          *)
Abort.
