Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
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
Require Import riscv.MkMachineWidth.
Require Import riscv.PseudoInstructions.
Require Import riscv.InstructionCoercions.
Require Import riscv.Program.
Require Import compiler.FlatToRiscvDef.
Require Import compiler.FlatToRiscv.
Require Import riscv.RiscvMachine.
Require Import riscv.MinimalMMIO.
Require Import compiler.FlatToRiscvDef.
Require Import riscv.AxiomaticRiscvMMIO.
Require Import riscv.runsToNonDet.
Require Import compiler.Rem4.
Require Import compiler.GoFlatToRiscv.

Import ListNotations.
Existing Instance DefaultRiscvState.


Module Type LEARNING.
  Parameter Learnt: Prop -> Prop.
  Parameter markLearnt: forall {P: Prop} (p: P), Learnt P.
End LEARNING.

Module Import Learning: LEARNING.
  Definition Learnt(P: Prop) := P.
  Definition markLearnt{P: Prop}(p: P): Learnt P := p.
End Learning.

Ltac learn_tac p H :=
  let P := type of p in
  lazymatch goal with
  | H: Learnt P |- _ => fail
  | |- _ =>
    let L := fresh "L" in
    pose proof (markLearnt p) as L; (* will stay around *)
    pose proof p as H (* will likely be destructed *)
  end.

Tactic Notation "learn" constr(p) := let H := fresh in learn_tac p H.
Tactic Notation "learn" constr(p) "as" ident(H) := learn_tac p H.

Ltac cheap_saturate :=
  unshelve (repeat match goal with
    | H: _ /\ _ |- _ => let Hl := fresh H "l" in let Hr := fresh H "r" in destruct H as [Hl Hr]
    | E: exists y, _ |- _ => let yf := fresh y in destruct E as [yf E]
    | H: forall (x: ?T), _ |- _ =>
      match type of T with
      | Prop => fail 1
      | _ => let x' := fresh x in (evar (x': T)); specialize (H x'); subst x'
      end
    | H1: _, H2: _ -> _ |- _ => let H3 := fresh H1 "_" H2 in learn (H2 H1) as H3
  end);
  [eauto..|].


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
    mem_ok :> map.ok mem;
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
  FlatToRiscvDef.compile_load sz x y := Lw x y 0; (* TODO respect access_size! *)
  FlatToRiscvDef.compile_store sz x y := Sw x y 0; (* TODO respect access_size! *)
  FlatToRiscvDef.compile_ext_call := compile_ext_call;
  FlatToRiscvDef.max_ext_call_code_size _ := 1;
|}).
  intros. unfold compile_ext_call.
  destruct f; destruct binds; try destruct binds;
  try destruct args; try destruct args; try destruct args;
  cbv; intros; discriminate.
Defined.

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
        (SLoop (SLoad Syntax.access_size.four _i _addr)
               (CondNez _i)
               (SSeq (SOp _s bopname.mul _i _i)
                     (SStore Syntax.access_size.four _addr _s)))).

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

Arguments Z.mul: simpl never.

Ltac head e :=
  match e with
  | ?f _ => head f
  | _ => e
  end.

Definition protected(P: Prop) := P.

Ltac protect_equalities :=
  repeat match goal with
         | H: ?a = ?b |- _ => change (protected (a = b)) in H
         end.

Ltac unprotect_equalities :=
  repeat match goal with
         | H: protected (?a = ?b) |- _ => change (a = b) in H
         end.

Ltac invert_hyp H := protect_equalities; inversion H; clear H; subst; unprotect_equalities.

Ltac invert_ind name :=
  match goal with
  | H: ?P |- _ =>
    let h := head P in constr_eq h name;
    invert_hyp H
  end.

Ltac destruct_unique_match :=
  let contrad := (exfalso; (contradiction || discriminate || congruence)) in
  match goal with
  | H: context[match ?e with _ => _ end] |- _ =>
    is_var e;
    destruct e;
    try contrad;
    let n := numgoals in guard n <= 1
  | H: context[match ?e with _ => _ end] |- _ =>
    let E := fresh "E" in destruct e eqn: E;
    try contrad;
    let n := numgoals in guard n <= 1
  end.

Ltac destruct_unique_matches := repeat destruct_unique_match.

Ltac contrad := contradiction || discriminate || congruence.

Arguments LittleEndian.combine: simpl never. (* TODO can we put this in word interface? *)
Arguments mcomp_sat: simpl never.

Definition TODO{T: Type}: T. Admitted.

Set Refine Instance Mode.
Instance FlatToRiscv_params: FlatToRiscv.parameters := (*unshelve refine ( *) {|
  FlatToRiscv.def_params := compilation_params;
  FlatToRiscv.locals := locals;
  FlatToRiscv.locals_ok := locals_ok;
  FlatToRiscv.mem := (@mem p);
  FlatToRiscv.mem_ok := mem_ok;
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
  unfold ZToReg, reg_eqb, remu, regToZ_unsigned, MachineWidth_XLEN in *.
  destruct_one_match.
  + (* TODO this should be just "word_solver" *)
    exfalso. apply Bool.negb_true_iff in E.
    apply reg_eqb_false in E.
    apply E; clear E.
    apply word.unsigned_inj.
    assert (4 mod 2 ^ width = 4) as F by apply TODO.
    rewrite word.unsigned_modu; rewrite word.unsigned_of_Z; rewrite F; [|lia].
    rewrite H.
    rewrite word.unsigned_of_Z.
    reflexivity.
  + reflexivity.
- intros. simpl. unfold default_translate.
  (*
  rewrite remu_def.
  rewrite Z.rem_mod_nonneg.
  + change (regToZ_unsigned (ZToWord 32 8)) with 8. rewrite H. reflexivity.
  + pose proof (regToZ_unsigned_bounds a). omega.
  + reflexivity.
  *)
  apply TODO.
- intros. simpl. unfold compile_ext_call.
  repeat destruct_one_match; rewrite? Zlength_cons; rewrite? Zlength_nil; cbv; congruence.
- apply TODO.
- apply TODO.
- intros initialL action.
  destruct initialL as [initialRegs initialPc initialNpc initialMem initialLog].
  destruct action; cbv [getRegs getPc getNextPc getMem getLog]; intros.
  + (* MMInput *)
    simpl in *|-.
    invert_ind @exec; [].
    simpl in *|-.
    repeat match goal with
           | l: list _ |- _ => destruct l;
                                 try (exfalso; (contrad || (cheap_saturate; contrad))); []
           end.
    destruct argvars; [| solve [exfalso; simpl in *; repeat destruct_unique_match] ].
    simpl in *|-.
    destruct_unique_match.
    replace r2 with r in * by congruence.
    destruct_products.
    repeat match goal with
           | H: Forall _ _ |- _ => apply Forall_singleton in H
           end.
    subst.
    eapply runsToNonDet.runsToStep; cycle 1.
    * intro mid.
      apply id.
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
      {
      rewrite left_identity. rewrite associativity.
      unfold getReg, State_is_RegisterFile.
      match goal with
      | H: ?a = Some ?b |- context [?a'] =>
        match a' with
        | map.get _ _ => replace a' with a by reflexivity; rewrite H
        end
      end.
      rename r into addr.
      replace (add addr (ZToReg 0)) with addr by apply TODO.
      apply go_loadWord_MMIO; [assumption..|].
      intro inp. cbv [getMem].
      eapply go_setRegister; [ assumption |].
      eapply go_step.
      eapply runsToNonDet.runsToDone.
      simpl.
      specialize (H15rrr (word.of_Z (BitOps.sextend 32 (LittleEndian.combine 4 inp)))).
      repeat split; auto.
      edestruct H16 as [ l' [A B] ]; [eauto|].
      destruct_unique_matches.
      invert_hyp E0.
      invert_hyp A.
      (* TODO do loadByte instead of loadWord to get rid of sign extension? *)
      match goal with
      | _: context[ [ ?a ] ] |- context[ [ ?a' ] ] =>
          let h :=  head a  in constr_eq h  @word.of_Z;
          let h' := head a' in constr_eq h' @word.of_Z;
          replace a' with a
      end; [exact B|].
      apply TODO.
      }
      {
        apply TODO.
      }
  + (* MMOutput *)
    apply TODO.
  Defined.

End MMIO1.
