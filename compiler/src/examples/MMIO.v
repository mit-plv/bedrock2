Require Import Coq.ZArith.ZArith.
Require Import coqutil.Macros.unique.
Require Import riscv.util.Word.
Require Import riscv.util.BitWidths.
Require Import compiler.util.Common.
Require Import compiler.Op.
Require Import bedrock2.Semantics.
Require Import riscv.util.Monads.
Require Import coqutil.Map.SortedList.
Require Import compiler.util.List_Set.
Require Import compiler.FlatImp.
Require Import riscv.util.ListLib.
Require Import riscv.Decode.
Require Import coqutil.sanity.
Require Import riscv.Utility.
Require Import riscv.PseudoInstructions.
Require Import riscv.InstructionCoercions.
Require Import riscv.Program.
Require Import compiler.FlatToRiscvDef.
Require Import compiler.FlatToRiscv.
Require Import riscv.RiscvMachine.
Require Import riscv.MinimalMMIO.
Require Import compiler.FlatToRiscvDef.
Require Import riscv.AxiomaticRiscv.
Require Import compiler.runsToNonDet.
Require Import compiler.containsProgram.
Import ListNotations.
Existing Instance DefaultRiscvState.

Open Scope ilist_scope.

Definition var: Type := Z.
Definition func: Type := Empty_set.

Instance act_dec: DecidableEq MMIOAction.
intros a b. destruct a; destruct b; (left + right); congruence.
Defined.

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

Instance myparams: Basic_bopnames.parameters := {|
  varname := var;
  funcname := func;
  actname := MMIOAction;
|}.

Module Import MMIO.
  Class parameters := {
    W :> Words;
    mem :> map.map word byte;
    BWS :> FlatToRiscvBitWidthSpecifics word;
    locals :> map.map var word;
    locals_ok :> map.ok locals;
    env :> map.map func (list var * list var * Syntax.cmd.cmd);
    env_ok :> map.ok env;
    interp_binop : bopname -> word -> word -> word;
  }.
End MMIO.

Section MMIO1.
  Context {p: unique! MMIO.parameters}.

  Definition magicMMIOAddrLit: Z := 65524.
  Definition simple_isMMIOAddr: word -> bool := word.eqb (word.of_Z magicMMIOAddrLit).

  Instance semantics_params: Semantics.parameters := {|
    Semantics.syntax := Basic_bopnames.make myparams;
    Semantics.width := width;
    Semantics.interp_binop := interp_binop;
    Semantics.funname_eqb f := Empty_set_rect _;
    Semantics.ext_spec t m action (argvals: list word) (post: (mem -> list word -> Prop)) :=
      match argvals with
      | addr :: _ =>
        simple_isMMIOAddr addr = true /\
        (* TODO this one says "exists addr in the 4-byte range which is undefined", but we probably
           need "forall addr in the 4 byte range, it is undefined" *)
        Memory.loadWord m addr = None /\
        match action with
        | MMInput => argvals = [addr] /\ forall val, post m [val]
        | MMOutput => exists val, argvals = [addr; val] /\ post m nil
        end
      | nil => False
      end;
  |}.

  (*
Instance myFlatImpParams: FlatImp.parameters := {|
  FlatImp.bopname_params := myparams;
  FlatImp.ext_spec := ext_spec;
|}.
*)

Instance compilation_params: FlatToRiscvDef.parameters. refine ({|
  FlatToRiscvDef.actname := MMIOAction;
  FlatToRiscvDef.LwXLEN := Lw;
  FlatToRiscvDef.SwXLEN := Sw;
  FlatToRiscvDef.compile_ext_call := compile_ext_call;
  FlatToRiscvDef.max_ext_call_code_size _ := 1;
|}). intros. abstract omega. Defined.

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
               (CondNez _i)
               (SSeq (SOp _s bopname.mul _i _i)
                     (SStore _addr _s)))).

Definition compiled: list Instruction := Eval cbv in compile_stmt squarer.

Print compiled.

(*
Section TODODontDuplicate.

  Let RiscvMachineL := RiscvMachine Register word32 MMIOAction.

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
*)

Lemma option_all_singleton: forall {A: Type} (a: A) (l: list (option A)),
    option_all l = Some [a] ->
    l = [Some a].
Proof.
  intros.
  destruct l; [|destruct l]; simpl in *; inversion H; destruct o; try congruence.
  destruct o0; destruct (option_all l); discriminate.
Qed.

Lemma map_singleton: forall {A B: Type} (f: A -> B) (l: list A) (b: B),
    List.map f l = [b] ->
    exists a, l = [a] /\ f a = b.
Proof.
  intros. destruct l; [|destruct l]; simpl in *; try discriminate; inversion H; eauto.
Qed.

Lemma Forall_singleton: forall {A: Type} (P: A -> Prop) (a: A),
    Forall P [a] ->
    P a.
Proof.
  intros. inversion H. assumption.
Qed.

Set Refine Instance Mode.
Instance FlatToRiscv_params: FlatToRiscv.parameters := (*unshelve refine ( *) {|
  FlatToRiscv.def_params := compilation_params;
  FlatToRiscv.locals := locals;
  FlatToRiscv.locals_ok := locals_ok;
  FlatToRiscv.mem := (@mem p);
  FlatToRiscv.actname_eq_dec := _;
  FlatToRiscv.BWS := BWS;
(*  FlatToRiscv.M := OStateND (RiscvMachine Register (Naive.word 32) MMIOAction);*)
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
- intros initialL action.
  destruct initialL as [initialRegs initialPc initialNpc initialIsMem initialMem initialLog].
  destruct action; cbv [getRegs getPc getNextPc isMem getMem getLog]; intros.
  + inversion H4; subst; clear H4.
    rename H13 into H4. simpl in H4.
    destruct H4 as (addr & E & IM & P). subst.
    apply option_all_singleton in H8.
    apply map_singleton in H8. destruct H8 as (a & ? & H8). subst.
    assert (exists resvar, resvars = [resvar]) as E. {
      specialize (P (ZToWord 32 0)).
      specialize H14 with (1 := P).
      destruct H14 as (? & ? & ?).
      clear -H.
      destruct resvars; [|destruct resvars]; simpl in H; inversion H; eauto.
    }
    destruct E as [resvar E]. subst.
    repeat match goal with
           | H: Forall _ _ |- _ => apply Forall_singleton in H
           end.
    simpl in H3.
    eapply runsToNonDet.runsToStep.
    * eapply go_fetch_inst; [reflexivity|eassumption|].
      cbv [Execute.execute ExecuteI.execute].
      rewrite associativity.
      eapply go_getRegister; [assumption|]. rewrite associativity.
      cbv [getRegs].
      match goal with
      | |- context [?T] =>
        match T with
        | translate Load ?w ?a => replace T with (Return a)
        end
      end.
      2: admit.
      rewrite left_identity. rewrite associativity.
      unfold getReg, State_is_RegisterFile.
      match goal with
      | H: ?a = Some ?b |- context [?a'] =>
        match a' with
        | @get _ _ _ _ _ => replace a' with a by reflexivity; rewrite H
        end
      end.
      unfold loadWord, IsRiscvMachineL.
      replace (add addr (ZToReg 0)) with addr by admit.


      admit. (* TODO interesting: how to get isMem/simple_isMMIOAddr compatibility?

   Probably not so relevant:
   to make load/store work in FlatToRiscv, some invariants about isMem will have to be
   carried around (similar to containsProgram invariants), and these will also have
   to be provided as a hypothesis to compile_ext_call_correct

   Relevant:
   ext_spec for MMIO should get the memory as an argument, and test that the address is
   not in the memory, and since we get an ext_spec here as a hypothesis, we can use this
   to replace "isMem mach addr" with "false"

   will require proper memory (map from address to byte)
 *)

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
