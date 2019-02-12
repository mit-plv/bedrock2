Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import coqutil.Macros.unique.
Require Import compiler.util.Common.
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
Require Import riscv.Primitives.
Require Import compiler.FlatToRiscvDef.
Require Import riscv.runsToNonDet.
Require Import compiler.Rem4.
Require Import compiler.GoFlatToRiscv.
Require Import compiler.SeparationLogic.
Require Import coqutil.Datatypes.Option.


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

Instance myparams: Syntax.parameters := {|
  Syntax.varname := var;
  Syntax.funname := func;
  Syntax.actname := MMIOAction;
|}.

Module Import MMIO.
  Class parameters := {
    W :> Words;
    mem :> map.map word byte;
    mem_ok :> map.ok mem;
    locals :> map.map var word;
    locals_ok :> map.ok locals;
    env :> map.map func (list var * list var * Syntax.cmd.cmd);
    env_ok :> map.ok env;
  }.
End MMIO.

Section MMIO1.
  Context {p: unique! MMIO.parameters}.

  Definition magicMMIOAddrLit: Z := 65524.
  Definition simple_isMMIOAddr: word -> bool := word.eqb (word.of_Z magicMMIOAddrLit).

  Instance semantics_params: Semantics.parameters := {|
    Semantics.syntax := myparams;
    Semantics.width := width;
    Semantics.funname_eqb f := Empty_set_rect _;
    Semantics.ext_spec t m action (argvals: list word) (post: (mem -> list word -> Prop)) :=
      match argvals with
      | addr :: _ =>
        simple_isMMIOAddr addr = true /\
        (* TODO this one says "exists addr in the 4-byte range which is undefined", but we probably
           need "forall addr in the 4 byte range, it is undefined" *)
        Memory.loadWord m addr = None /\ (* <-- TODO move to ext_guarantee *)
        match action with
        | MMInput => argvals = [addr] /\ forall val, post m [val]
        | MMOutput => exists val, argvals = [addr; val] /\ post m nil
        end
      | nil => False
      end;
  |}.

Instance compilation_params: FlatToRiscvDef.parameters. refine ({|
  FlatToRiscvDef.actname := MMIOAction;
  FlatToRiscvDef.compile_ext_call := compile_ext_call;
  FlatToRiscvDef.max_ext_call_code_size _ := 1;
|}).
  intros. unfold compile_ext_call.
  destruct f; destruct binds; try destruct binds;
  try destruct args; try destruct args; try destruct args;
  cbv; intros; discriminate.
Defined.

(*
addr = magicMMIOAddr;
loop {
  i = input addr;
  stay in loop only if i is non-zero;
  s = i * i;
  output addr s;
}
*)

Definition _addr: Syntax.varname := 1.
Definition _i: Syntax.varname := 2.
Definition _s: Syntax.varname := 3.

Definition squarer: stmt :=
  (SSeq (SLit _addr magicMMIOAddrLit)
        (SLoop (SLoad Syntax.access_size.four _i _addr)
               (CondNez _i)
               (SSeq (SOp _s Syntax.bopname.mul _i _i)
                     (SStore Syntax.access_size.four _addr _s)))).

Definition compiled: list Instruction := Eval cbv in compile_stmt RV32IM squarer.

Print compiled.

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
(*  FlatToRiscv.M := OStateND (RiscvMachine Register (Naive.word 32) MMIOAction);*)
  FlatToRiscv.MM := OStateND_Monad _;
  FlatToRiscv.RVM := IsRiscvMachineL;
  FlatToRiscv.PR := MinimalMMIOSatisfiesPrimitives;
  FlatToRiscv.ext_spec := ext_spec;
|}.
- apply TODO.
- apply TODO.
- evar (ext_guarantee: RiscvMachine Register FlatToRiscvDef.actname -> Prop).
  exact ext_guarantee.
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
    * eapply go_fetch_inst; [reflexivity| | |].
      { simpl in *. ecancel_assumption. }
      { unfold valid_register in *.
        cbv -[Z.lt Z.le]; repeat split; auto; try lia. }
      cbv [Execute.execute ExecuteI.execute].
      rewrite associativity.
      eapply go_getRegister; [eassumption..|]. rewrite associativity.
      cbv [getRegs].
      match goal with
      | |- context [?T] =>
        match T with
        | translate Load ?w ?a => replace T with (Return a)
        end
      end.
      {
      rewrite left_identity. rewrite associativity.
      rename r into addr.
      replace (add addr (ZToReg 0)) with addr by apply TODO.
      apply spec_Bind.
      refine (ex_intro _ (fun v m => m = _) _).
      split.
      - apply spec_loadWord. simpl. right. repeat split; try assumption.
        (* TODO use ext_guarantee here *) admit.
      - intros. subst. apply go_setRegister; [assumption|].
        apply go_step.
        apply runsToDone.
        simpl.
        repeat split.
        + unfold mmioLoadEvent.
          specialize (H16 initialMem [signedByteTupleToReg a]).
          destruct H16 as [ l' [A B] ].
          { (* TODO trace translation *) admit. }
          { inversion_option.
            subst l'.
            Fail exact B.
            (* TODO trace translation *) admit. }
        + rewrite Zlength_cons, Zlength_nil. apply TODO. (* TODO word solver *)
        + rewrite Zlength_cons, Zlength_nil. apply TODO. (* TODO word solver *)
        + simpl in *. seplog.
        + admit. (* prove ext_guarantee preservation *)
      }
      { reflexivity. }
  + (* MMOutput *)
    apply TODO.
  - (* go_load *)
    apply TODO.
  - (* go_store *)
    apply TODO.
  Admitted.

End MMIO1.
