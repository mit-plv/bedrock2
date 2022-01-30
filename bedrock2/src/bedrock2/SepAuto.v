(* More separation logic automation, independent of the programming language semantics,
   and intended to be usable both for concrete programs and simulation proofs.

   Note: If after importing this file, you import coqutil.Tactics.fwd_core or another
   file which exports coqutil.Tactics.fwd_core (eg coqutil.Tactics.fwd), that will
   undo the `Ltac fwd_rewrites ::= fwd_rewrite_db_in_star.` patching, so `fwd` and
   tactics using `fwd` will do fewer simplifications than intended *)

Require Export Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import coqutil.Z.Lia.
Require Export coqutil.Byte.
Require Import coqutil.Datatypes.HList.
Require Import coqutil.Datatypes.PropSet.
Require Export coqutil.Datatypes.Inhabited.
Require Import coqutil.Tactics.Tactics coqutil.Tactics.rewr coqutil.Tactics.rdelta.
Require Import Coq.Program.Tactics.
Require Export coqutil.Tactics.autoforward.
Require Export coqutil.Map.Interface coqutil.Map.Properties coqutil.Map.OfListWord.
Require Export coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Sorting.OrderToPermutation.
Require Export coqutil.Tactics.fwd.
Require Import coqutil.Tactics.ltac_list_ops.
Require Export bedrock2.Lift1Prop.
Require Export bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
Require Import bedrock2.Array.
Require Export bedrock2.ZnWords.
Require Import bedrock2.ptsto_bytes bedrock2.Scalars.
Export List.ListNotations. Open Scope list_scope.

Ltac fwd_rewrites ::= fwd_rewrite_db_in_star.

Module Export SepLogPredsWithAddrLast. Section __.
  Context {width : Z} {word : Word.Interface.word width} {mem : map.map word byte}.

  Definition at_addr(addr: word)(clause: word -> mem -> Prop): mem -> Prop := clause addr.

  (* Redefinitions to change order of arguments to put address last *)

  Definition ptsto_bytes (n : nat) (value : tuple byte n) (addr : word) : mem -> Prop :=
    ptsto_bytes n addr value.

  Definition littleendian (n : nat) (value : Z) (addr : word) : mem -> Prop :=
    littleendian n addr value.

  Definition truncated_scalar sz (value : Z) addr : mem -> Prop :=
    truncated_scalar sz addr value.

  Definition truncated_word sz (value: word) addr : mem -> Prop :=
    truncated_word sz addr value.

  Definition scalar16 := truncated_word Syntax.access_size.two.
  Definition scalar32 := truncated_word Syntax.access_size.four.
  Definition scalar := truncated_word Syntax.access_size.word.
End __. End SepLogPredsWithAddrLast.

(* `*` is at level 40, and we want to bind stronger than `*`, and moreover,
   `^` is at level 30, and for consistency, we also want to bind stronger than `^`,
   so we choose 25 *)
Notation "addr |-> clause" := (at_addr addr clause)
  (at level 25,
   format "addr  |->  '[' clause ']'").

Inductive get_option{A: Type}: option A -> (A -> Prop) -> Prop :=
| mk_get_option: forall (a: A) (post: A -> Prop), post a -> get_option (Some a) post.

Section SepLog.
  Context {width: Z} {word: word.word width} {mem: map.map word byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Lemma load_of_sep_cps: forall sz addr value R m (post: word -> Prop),
      sep (addr |-> truncated_word sz value) R m /\ post (truncate_word sz value) ->
      get_option (Memory.load sz m addr) post.
  Proof.
    intros. destruct H. eapply load_of_sep in H. rewrite H.
    constructor. assumption.
  Qed.

  Lemma load_word_of_sep_cps: forall addr value R m (post: word -> Prop),
      sep (addr |-> scalar value) R m /\ post value ->
      get_option (Memory.load Syntax.access_size.word m addr) post.
  Proof.
    intros. destruct H. eapply load_word_of_sep in H. rewrite H.
    constructor. assumption.
  Qed.

  Lemma store_word_of_sep_cps_two_subgoals: forall addr oldvalue newvalue R m (post: mem -> Prop),
      seps [addr |-> scalar oldvalue; R] m ->
      (forall m', seps [addr |-> scalar newvalue; R] m' -> post m') ->
      get_option (Memory.store Syntax.access_size.word m addr newvalue) post.
  Proof.
    intros. eapply Scalars.store_word_of_sep in H. 2: eassumption.
    destruct H as (m1 & E & P). rewrite E. constructor. exact P.
  Qed.

  Lemma store_word_of_sep_cps: forall addr oldvalue newvalue R m (post: mem -> Prop),
      seps [addr |-> scalar oldvalue; R;
            emp (forall m', seps [addr |-> scalar newvalue; R] m' -> post m')] m ->
      get_option (Memory.store Syntax.access_size.word m addr newvalue) post.
  Proof.
    intros. unfold seps in H. apply sep_assoc in H. apply sep_emp_r in H. destruct H.
    eapply store_word_of_sep_cps_two_subgoals. 1: unfold seps. 1: eassumption. eassumption.
  Qed.

  (* R, typically instantiated to `seps [whatever; is; left]`, appears twice:
     On the left of the impl1 (this determines its value), and as the first
     element of the `seps` on the right (there, it is an evar for the frame).
     P is the continuation postcondition. *)
  Lemma impl1_done: forall (R: mem -> Prop) (P: Prop),
      P -> impl1 R (seps [R; emp P]).
  Proof.
    unfold impl1, seps. intros. apply sep_emp_r. auto.
  Qed.

  (* All arguments except stmt are just ghost parameters to guide typeclass search.
     The shape of stmt will typically be
       forall valAll valPart valFrame1 ... valFrameN,
         sidecondition saying that assembling valPart valFrame1 ... valFrameN = valAll ->
         iff1 (seps [addrPart |-> predPart valPart; Frame...]) (addrAll |-> predAll valAll)
     but since that's a variable number of universally quantified variables, it would
     be a bit cumbersome to enforce that shape, and since it's not needed to enforce it,
     we don't. *)
  Definition split_sepclause{TypeAll TypePart: Type}
             (addrAll : word)(predAll : TypeAll  -> word -> mem -> Prop)
             (addrPart: word)(predPart: TypePart -> word -> mem -> Prop)
             (stmt: Prop) := stmt.

  Local Set Warnings "-notation-overridden".
  Local Infix "++" := SeparationLogic.app. Local Infix "++" := app : list_scope.
  Let nth n xs := SeparationLogic.hd (emp(map:=mem) True) (SeparationLogic.skipn n xs).
  Let remove_nth n (xs : list (mem -> Prop)) :=
    (SeparationLogic.firstn n xs ++ SeparationLogic.tl (SeparationLogic.skipn n xs)).

  Lemma rewrite_ith_in_lhs_of_impl1: forall i Ps Pi Qs R,
      nth i Ps = Pi ->
      iff1 (seps Qs) Pi -> (* <-- used right-to-left *)
      impl1 (seps (remove_nth i Ps ++ Qs)) R ->
      impl1 (seps Ps) R.
  Proof.
    intros. subst Pi.
    unfold nth, remove_nth in *.
    rewrite <-(seps_nth_to_head i Ps).
    rewrite <- H0.
    rewrite 2seps_app in H1. rewrite seps_app.
    etransitivity. 2: eassumption.
    ecancel.
  Qed.
End SepLog.

(* Hints for `(split_sepclause ?addrAll ?predAll ?addrPart ?predPart ?stmt)` goals *)
Create HintDb split_sepclause_goal.

(* Hints to solve the sideconditions of the `stmt` above, when using the iff1
   right-to-left, ie in the split direction *)
Create HintDb split_sepclause_sidecond.

(* Hints to solve the sideconditions of the `stmt` above, when using the iff1
   left-to-right, ie in the merge direction *)
Create HintDb merge_sepclause_sidecond.

(* Poses split_sepclause lemmas as hypotheses in the context, forming a stack of
   rewrite steps that have been performed, which can later be undone by
   pop_split_sepclause_stack *)
Ltac impl_ecancel_step_with_splitting :=
  lazymatch goal with
  | |- Lift1Prop.impl1 (seps ?L) (seps ((?addrR |-> ?predR ?valR) :: ?RRest)) =>
    let iLi := index_and_element_of L in (* <-- multi-success! *)
    let i := lazymatch iLi with (?i, _) => i end in
    let Li := lazymatch iLi with (_, ?Li) => Li end in
    let Li := eval cbn [hd app firstn tl skipn] in Li in
    lazymatch Li with
    (* Simplifying assumption: Only the last argument to predL is a value that
       can be changed by stores and function calls, all other arguments are constants *)
    | ?addrL |-> ?predL ?valL =>
        let Sp := fresh "Sp" in
        eassert (split_sepclause addrL predL addrR predR _) as Sp
            (* typeclasses eauto instead of eauto because eauto unfolds split_sepclause
               and then just does `exact H` for the last Prop in the context, and it
               seems that `Hint Opaque` and `Hint Constants Opaque` don't fix that
               (and `Opaque split_sepclause` would fix it, but also affects the conversion
               algorithm) *)
            by typeclasses eauto with split_sepclause_goal;
        eapply (rewrite_ith_in_lhs_of_impl1 i L Li);
        cbn [hd app firstn tl skipn];
        [ reflexivity
        | cbv [split_sepclause] in Sp;
          eapply Sp;
          solve [eauto with split_sepclause_sidecond]
        | ]
    end
  end.

Ltac ecancel_with_remaining_emp_Prop :=
  cancel_seps;
  repeat (repeat ecancel_step_by_implication; try impl_ecancel_step_with_splitting);
  refine (impl1_done _ _ _).

Ltac ecancel_assumption_with_remaining_emp_Prop :=
  match goal with
  | H: seps _ ?m |- seps _ ?m =>
    refine (Morphisms.subrelation_refl Lift1Prop.impl1 _ _ _ m H)
  end;
  ecancel_with_remaining_emp_Prop.

Ltac clear_split_sepclause_stack :=
  repeat match goal with
         | H: split_sepclause _ _ _ _ _ |- _ => clear H
         end.

Ltac pop_split_sepclause_stack :=
  let H := lazymatch goal with H: seps _ ?m |- _ => H end in
  let Sp := lazymatch goal with Sp: split_sepclause _ _ _ _ _ |- _ => Sp end in
  ((cbv [split_sepclause] in Sp;
    cbn [seps] in Sp, H;
    seprewrite_in_by Sp H ltac:(eauto with merge_sepclause_sidecond)
   ) || let T := type of Sp in idtac "Note: Failed to merge sep clauses using" T);
  clear Sp.

Lemma iff1_refl{A: Type}(P: A -> Prop): iff1 P P. Proof. reflexivity. Qed.
Lemma iff1_sym{A: Type}{P Q: A -> Prop}: iff1 P Q -> iff1 Q P.
Proof. intros. symmetry. assumption. Qed.

Ltac iff1_syntactic_reflexivity :=
  lazymatch goal with
  | |- iff1 ?x ?y => first [is_evar x | is_evar y | constr_eq x y]
  end;
  exact (iff1_refl _).

(* Given `H: seplogformula m`, first cbns away all occurrences of `seps` in H,
   and then flattens the formula into a list of sep clauses, resulting in an
   `H: seps [...] m` *)
Ltac flatten_seps_in H :=
  lazymatch type of H with
  | ?nested ?m =>
    let tmem := type of m in
    let E := fresh "E" in
    eassert (@iff1 tmem nested _) as E;
    [ (* from `nested` to `Tree.to_sep tree` *)
      let stars := eval cbn[seps] in nested in
      let tree := reify stars in
      transitivity (Tree.to_sep tree); [
        cbn [seps Tree.to_sep Tree.interp]; iff1_syntactic_reflexivity
      |];
      (* from `Tree.to_sep tree` to `seps (Tree.flatten tree)` *)
      transitivity (seps (Tree.flatten tree)); [
        exact (iff1_sym (Tree.flatten_iff1_to_sep tree))
      |];
      (* from `seps (Tree.flatten tree)` to `seps clauses` *)
      cbn [SeparationLogic.Tree.flatten SeparationLogic.Tree.interp SeparationLogic.app];
      iff1_syntactic_reflexivity
    | let HNew := fresh in pose proof (proj1 (E m) H) as HNew;
      clear E H;
      rename HNew into H ]
  end.


(* Applying the order of sep clauses from an old hypothesis onto a new hypothesis: *)

Section TransferSepsOrder.
  Context {width : Z} {word : Word.Interface.word width} {word_ok: word.ok word}
          {mem : map.map word byte} {mem_ok: map.ok mem}.

  Lemma reorder_is_iff1: forall (order: list nat) (l: list (mem -> Prop)),
      List.length order = List.length l ->
      iff1 (seps l) (seps (reorder order l)).
  Proof.
    intros. rewrite <-2seps'_iff1_seps. rewrite seps'_fold_right.
    rewrite reorder_comm_fold_right.
    - reflexivity.
    - intros. eapply iff1ToEq. cancel.
    - assumption.
  Qed.
End TransferSepsOrder.

Ltac clause_index clause clauses start_index default_index :=
  lazymatch clauses with
  | cons (at_addr ?a _) ?tail =>
    lazymatch clause with
    | at_addr a _ => constr:(start_index)
    | _ => clause_index clause tail (S start_index) default_index
    end
  | cons clause _ => constr:(start_index)
  | cons _ ?tail => clause_index clause tail (S start_index) default_index
  | nil => constr:(default_index)
  end.

Ltac get_order_rec old_clauses new_clauses default_index :=
  lazymatch new_clauses with
  | nil => constr:(@nil nat)
  | cons ?clause ?tail =>
    let priority := clause_index clause old_clauses 0%nat default_index in
    let rest := get_order_rec old_clauses tail priority in
    constr:(priority :: rest)
  end.

Ltac get_order old_clauses new_clauses :=
  (* if the first clause is not found in old_clauses, we put it at the end;
     if a non-first clause is not found, we put it after the clause that's
     to the left of it in new_clauses, so we give it the same priority value,
     so the returned order might have duplicate priority values, and we rely
     on mergesort being stable to keep the order between clauses of the same priority *)
  let n := list_length old_clauses in
  get_order_rec old_clauses new_clauses n.

Ltac is_fresh x := assert_succeeds (pose proof tt as x).

Ltac make_fresh x :=
  tryif is_fresh x then idtac else let x' := fresh x "_0" in rename x into x'.

(* Given an old and a new sep hyp, transfers the order of the sepclauses from the old one
   to the new one *)
Ltac transfer_sep_order_from_to HOld HNew :=
  lazymatch type of HOld with
  | seps ?old_clauses ?mOld =>
    lazymatch type of HNew with
    | seps ?new_clauses ?mNew =>
      let tmem := type of mNew in
      let E := fresh "E" in
      eassert (@iff1 tmem (seps new_clauses) _) as E;
      [ (* from `seps new_clauses` to `seps (reorder order new_clauses)` *)
        let order := get_order old_clauses new_clauses in
        etransitivity; [
          eapply (reorder_is_iff1 order new_clauses); reflexivity
        |];
        (* from `seps (reorder order new_clauses)` to cbv'd version of it *)
        cbv [reorder];
        let r := eval vm_compute in (order_to_permutation order) in
            change (order_to_permutation order) with r;
        cbv [apply_permutation apply_permutation_with_default my_list_map my_list_nth];
        reflexivity
      | let HNewNew := fresh in pose proof (proj1 (E mNew) HNew) as HNewNew;
        clear E HOld HNew;
        try clear mOld;
        make_fresh mOld;
        rename HNewNew into HOld, mNew into mOld ]
    end
  end.

Section TestTransferSepsOrder.
  Context {width : Z} {word : Word.Interface.word width} {word_ok: word.ok word}
          {mem : map.map word byte} {mem_ok: map.ok mem}.

  Lemma reordering_test: forall addr1 addr2 addr3 addr4 v1_old v1_new v2 v3 v4 R (m m': mem),
    seps [addr1 |-> scalar v1_old; addr2 |-> scalar v2; addr3 |-> scalar v3; R] m ->
    (* value at addr1 was updated, addr2 was consumed, addr4 was added, and order changed: *)
    seps [R; seps [addr3 |-> scalar v3; addr4 |-> scalar v4]; addr1 |-> scalar v1_new] m' ->
    (* desired order:
    seps [addr1 |-> scalar v1_new; addr3 |-> scalar v3; addr4 |-> scalar v4; R] m1 *)
    True ->
    True.
  Proof.
    intros *. intros M M2 ExtraHyp.
    (*            0                        1                    2                    3
       M  : seps [addr1 |-> scalar v1_old; addr2 |-> scalar v2; addr3 |-> scalar v3; R] m0
       M2 : seps [R; addr3 |-> scalar v3; addr4 |-> scalar v4; addr1 |-> scalar v1_new] m1
       order :=  [3; 2;                   2;                   0                      ] *)
    flatten_seps_in M2.
    transfer_sep_order_from_to M M2.
    lazymatch type of M with
    | seps [addr1 |-> scalar v1_new; addr3 |-> scalar v3; addr4 |-> scalar v4; R] m => idtac
    end.
  Abort.
End TestTransferSepsOrder.
