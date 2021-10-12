Require Import Coq.ZArith.ZArith.
Require Import compiler.FlatImp.
Require Import coqutil.Decidable.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.simpl_rewrite.
Require Import Coq.Lists.List. Import ListNotations.
Require Import riscv.Utility.Utility.
Require Import coqutil.Z.Lia.
Require Import coqutil.Macros.unique.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Map.Solver.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Map.MapEauto.
Require Import bedrock2.Syntax.
Require Import coqutil.Datatypes.ListSet.
Require Import coqutil.Tactics.Simp.
Require Import coqutil.Tactics.autoforward.
Require Import compiler.Simulation.
Require Import compiler.Registers.

Open Scope Z_scope.

Local Notation srcvar := String.string (only parsing).
Local Notation impvar := Z (only parsing).
Local Notation stmt  := (@FlatImp.stmt srcvar). (* input type *)
Local Notation stmt' := (@FlatImp.stmt impvar). (* output type *)
Local Notation bcond  := (@FlatImp.bcond srcvar).
Local Notation bcond' := (@FlatImp.bcond impvar).

Definition accessed_vars_bcond(c: bcond): list srcvar :=
  match c with
  | CondBinary _ x y => list_union String.eqb [x] [y]
  | CondNez x => [x]
  end.

Fixpoint live(s: stmt)(used_after: list srcvar): list srcvar :=
  match s with
  | SSet x y
  | SLoad _ x y _
  | SInlinetable _ x _ y =>
    list_union String.eqb [y] (list_diff String.eqb used_after [x])
  | SStore _ a x _ => list_union String.eqb [a; x] used_after
  | SStackalloc x _ body => list_diff String.eqb (live body used_after) [x]
  | SLit x _ => list_diff String.eqb used_after [x]
  | SOp x _ y z => list_union String.eqb [y; z] (list_diff String.eqb used_after [x])
  | SIf c s1 s2 => list_union String.eqb
                              (list_union String.eqb (live s1 used_after) (live s2 used_after))
                              (accessed_vars_bcond c)
  | SSeq s1 s2 => live s1 (live s2 used_after)
  | SLoop s1 c s2 =>
    live s1 (list_union String.eqb (accessed_vars_bcond c) (list_union String.eqb used_after (live s2 [])))
  | SSkip => used_after
  | SCall binds _ args
  | SInteract binds _ args => list_union String.eqb args (list_diff String.eqb used_after binds)
  end.

(* old RegAlloc files:
https://github.com/mit-plv/bedrock2/tree/7cbae1a1caf7d19270d0fb37199f86eb8ea5ce4f/compiler/src/compiler
*)

(* Simplification: For each source variable, we only create one live interval, and extend it
   far enough to cover all actual live intervals (keeping several live intervals per srcvar
   would be tricky because an interval could have two different start points (one in a
   then-branch, the other in an else-branch of an if), but a common end point after the if),
   in the simplified version, we just say that the live interval starts in the then branch,
   which appears first according to the chosen linearization order). *)

Definition event: Type := srcvar * bool. (* bool stands for is_start *)

(* start_event inserts a start event directly followed by an end event.
   The end event is needed because we don't do dead code elimination, and we need
   to avoid that an assignment to a variable that's never read after the assignment
   does not invalidate another register, so we extend the live interval of each
   variable all the way to that unused assignment, so that the register assigned to x
   is not reused too early. *)
Definition start_event(x: srcvar): list event := [(x, true); (x, false)].
Definition end_event(x: srcvar): list event := [(x, false)].

Definition bcond_events(c: bcond)(after: list event): list event :=
  match c with
  | CondBinary _ x y => end_event x ++ end_event y ++ after
  | CondNez x => end_event x ++ after
  end.

(* incorrect without filtering (assumes that each read event is the last read of that variable) *)
Fixpoint events(s: stmt)(after: list event): list event :=
  match s with
  | SSet x y
  | SLoad _ x y _ => end_event y ++ start_event x ++ after
  (* Note: we deliberately flip the order of (start_event x) and (end_event y) for SInlinetable
     to make sure they are considered live at the same time, so that they don't get assigned to
     the same register, so that the x<>y sidecondition of exec.inlinetable is preserved *)
  | SInlinetable _ x _ y => start_event x ++ end_event y ++ after
  | SStore _ a x _ => end_event a ++ end_event x ++ after
  | SStackalloc x _ body => start_event x ++ events body after
  | SLit x _ => start_event x ++ after
  | SOp x _ y z => end_event y ++ end_event z ++ start_event x ++ after
  | SIf c s1 s2 => bcond_events c (events s1 (events s2 after))
  | SSeq s1 s2 => events s1 (events s2 after)
  | SLoop s1 c s2 =>
    (* unroll loop twice so that it becomes apparent how (i+1)-th iteration depends on i-th iteration *)
    events s1 (bcond_events c (events s2 (
    events s1 (bcond_events c (events s2 (
    events s1 (bcond_events c after)))))))
  | SSkip => after
  | SCall binds _ args
  | SInteract binds _ args => List.flat_map end_event args ++ List.flat_map start_event binds ++ after
  end.

Fixpoint remove_nonfirst_starts(started: list srcvar)(l: list event): list event :=
  match l with
  | (x, is_start) :: rest =>
    if is_start then
      if List.find (String.eqb x) started then
        remove_nonfirst_starts started rest
      else
        (x, true) :: remove_nonfirst_starts (x :: started) rest
    else
      (x, false) :: remove_nonfirst_starts started rest
  | nil => nil
  end.

Fixpoint remove_nonlast_ends(l: list event): list event :=
  match l with
  | (x, is_start) :: rest =>
    if is_start then
      (x, true) :: remove_nonlast_ends rest
    else
      if List.find (fun '(y, y_is_start) => andb (negb y_is_start) (String.eqb x y)) rest then
        remove_nonlast_ends rest
      else
        (x, false) :: remove_nonlast_ends rest
  | nil => nil
  end.

Definition intervals(input_vars: list srcvar)(s: stmt)(output_vars: list srcvar): list event :=
  let unfiltered := List.flat_map start_event input_vars ++ (events s (List.flat_map end_event output_vars)) in
  remove_nonfirst_starts [] (remove_nonlast_ends unfiltered).

Declare Scope option_monad_scope. Local Open Scope option_monad_scope.

Notation "' pat <- c1 ;; c2" :=
  (match c1 with
   | Some pat => c2
   | None => None
   end)
  (at level 61, pat pattern, c1 at next level, right associativity) : option_monad_scope.

Notation "x <- c1 ;; c2" :=
  (match c1 with
   | Some x => c2
   | None => None
   end)
  (at level 61, c1 at next level, right associativity) : option_monad_scope.

Notation "c1 ;; c2" :=
  (match c1 with
   | Some _ => c2
   | None => None
   end)
  (at level 61, right associativity) : option_monad_scope.

(* TODO: once spilling is changed, this will change too *)
Definition not_reserved(x: Z): bool := 5 <? x.

Definition temp_regs : list impvar := Eval compute in List.filter not_reserved (reg_class.all reg_class.temp).
Definition saved_regs: list impvar := Eval compute in List.filter not_reserved (reg_class.all reg_class.saved).
Definition arg_regs  : list impvar := Eval compute in List.filter not_reserved (reg_class.all reg_class.arg).

(* Register availability, split by how preferable they are.
   For simplicity, we use the argument registers *only* for argument passing and as spilling temporaries. *)
Record av_regs := mk_av_regs {
  av_saved_regs: list impvar;
  av_temp_regs: list impvar;
  av_stack_slots: list impvar;
  first_fresh_stack_slot: impvar;
}.

Definition initial_av_regs := {|
  av_saved_regs := saved_regs;
  av_temp_regs := temp_regs;
  av_stack_slots := [];
  first_fresh_stack_slot := 32;
|}.

Definition acquire_reg(av: av_regs): impvar * av_regs :=
  match av with
  | mk_av_regs av_saved_regs av_temp_regs av_stack_slots ff =>
    match av_saved_regs with
    | x :: xs => (x, mk_av_regs xs av_temp_regs av_stack_slots ff)
    | nil =>
      match av_temp_regs with
      | x :: xs => (x, mk_av_regs nil xs av_stack_slots ff)
      | nil =>
        match av_stack_slots with
        | x :: xs => (x, mk_av_regs nil nil xs ff)
        | nil => (ff, mk_av_regs nil nil nil (ff+1))
        end
      end
    end
  end.

Definition yield_reg(r: impvar)(av: av_regs): av_regs :=
  match av with
  | mk_av_regs av_saved_regs av_temp_regs av_stack_slots ff =>
    match reg_class.get r with
    | reg_class.saved => mk_av_regs (r :: av_saved_regs) av_temp_regs av_stack_slots ff
    | reg_class.temp => mk_av_regs av_saved_regs (r :: av_temp_regs) av_stack_slots ff
    | reg_class.stack_slot => mk_av_regs av_saved_regs av_temp_regs (r :: av_stack_slots) ff
    | _ => av
    end
  end.

Definition lookup(x: srcvar)(corresp: list (srcvar * impvar)): option impvar :=
  match List.find (fun p => String.eqb x (fst p)) corresp with
  | Some (_, x') => Some x'
  | None => None
  end.

Definition lookups(xs: list srcvar)(corresp: list (srcvar * impvar)): option (list impvar) :=
  List.option_all (List.map (fun arg => lookup arg corresp) xs).

Fixpoint process_intervals(corresp: list (srcvar * impvar))(av: av_regs)(l: list event):
  list (srcvar * impvar) :=
  match l with
  | (x, is_start) :: rest =>
    if is_start then
      let (y, av) := acquire_reg av in process_intervals ((x, y) :: corresp) av rest
    else
      let av := match lookup x corresp with
                | Some y => yield_reg y av
                | None => av (* unexpected: end_event without start_event *)
                end in
      process_intervals corresp av rest
  | nil => corresp
  end.

Definition rename_bcond(corresp: list (srcvar * impvar))(c: bcond): option bcond' :=
  match c with
  | CondBinary op y z =>
    y' <- lookup y corresp;;
    z' <- lookup z corresp;;
    Some (CondBinary op y' z')
  | CondNez y =>
    y' <- lookup y corresp;;
    Some (CondNez y')
  end.

Fixpoint rename(corresp: list (srcvar * impvar))(s: stmt): option stmt' :=
  match s with
  | SLoad sz x y ofs =>
    x' <- lookup x corresp;;
    y' <- lookup y corresp;;
    Some (SLoad sz x' y' ofs)
  | SStore sz x y ofs =>
    x' <- lookup x corresp;;
    y' <- lookup y corresp;;
    Some (SStore sz x' y' ofs)
  | SInlinetable sz x bs y =>
    x' <- lookup x corresp;;
    y' <- lookup y corresp;;
    Some (SInlinetable sz x' bs y')
  | SStackalloc x n body =>
    x' <- lookup x corresp;;
    body' <- rename corresp body;;
    Some (SStackalloc x' n body')
  | SLit x z =>
    x' <- lookup x corresp;;
    Some (SLit x' z)
  | SOp x op y z =>
    x' <- lookup x corresp;;
    y' <- lookup y corresp;;
    z' <- lookup z corresp;;
    Some (SOp x' op y' z')
  | SSet x y =>
    x' <- lookup x corresp;;
    y' <- lookup y corresp;;
    Some (SSet x' y')
  | SIf c s1 s2 =>
    c' <- rename_bcond corresp c;;
    s1' <- rename corresp s1;;
    s2' <- rename corresp s2;;
    Some (SIf c' s1' s2')
  | SLoop s1 c s2 =>
    s1' <- rename corresp s1;;
    c' <- rename_bcond corresp c;;
    s2' <- rename corresp s2;;
    Some (SLoop s1' c' s2')
  | SSeq s1 s2 =>
    s1' <- rename corresp s1;;
    s2' <- rename corresp s2;;
    Some (SSeq s1' s2')
  | SSkip =>
    Some SSkip
  | SCall binds f args =>
    args' <- lookups args corresp;;
    binds' <- lookups binds corresp;;
    Some (SCall binds' f args')
  | SInteract binds f args =>
    args' <- lookups args corresp;;
    binds' <- lookups binds corresp;;
    Some (SInteract binds' f args')
  end.

Module WithBugs.
Definition assign_lhs(x: srcvar)(corresp: list (srcvar * impvar))(av: av_regs) :=
  match lookup x corresp with
  | Some x' => (x', corresp, av)
  | None => let '(x', av) := acquire_reg av in (x', (x, x') :: corresp, av)
  end.

Fixpoint assign_lhss(xs: list srcvar)(corresp: list (srcvar * impvar))(av: av_regs):
  (list impvar * list (srcvar * impvar) * av_regs) :=
  match xs with
  | nil => (nil, corresp, av)
  | h :: t => let '(y, corresp, av) := assign_lhs h corresp av in
              let '(ys, corresp, av) := assign_lhss t corresp av in
              (y :: ys, corresp, av)
  end.

Fixpoint regalloc
         (corresp: list (srcvar * impvar))  (* current mapping *)
         (av: av_regs)                      (* available registers *)
         (s: stmt)                          (* statement to be register allocated *)
         (l_after: list srcvar):            (* variables that are live after s *)
  option (list (srcvar * impvar) * av_regs * stmt') := (* should aways return Some *)
  let l_before := live s l_after in
  let av := List.fold_right
              (fun p av => if List.find (String.eqb (fst p)) l_before then av else yield_reg (snd p) av)
              av corresp in
  let corresp := List.filter
                   (fun p => if List.find (String.eqb (fst p)) l_before then true else false) corresp in
  match s with
  | SLoad sz x y ofs =>
    y' <- lookup y corresp;;
    let '(x', corresp, av) := assign_lhs x corresp av in
    Some (corresp, av, SLoad sz x' y' ofs)
  | SStore sz x y ofs =>
    x' <- lookup x corresp;;
    y' <- lookup y corresp;;
    Some (corresp, av, SStore sz x' y' ofs)
  | SInlinetable sz x bs y =>
    (* Note: We expect that x<>y and that the srcvar->impvar mapping in corresp is injective,
       so we get x'<>y', which is required by exec.inlinetable *)
    y' <- lookup y corresp;;
    let '(x', corresp, av) := assign_lhs x corresp av in
    Some (corresp, av, SInlinetable sz x' bs y')
  | SStackalloc x n body =>
    let '(x', corresp, av) := assign_lhs x corresp av in
    '(corresp, av, body') <- regalloc corresp av body l_after;;
    Some (corresp, av, SStackalloc x' n body')
  | SLit x z =>
    let '(x', corresp, av) := assign_lhs x corresp av in
    Some (corresp, av, SLit x' z)
  | SOp x op y z =>
    y' <- lookup y corresp;;
    z' <- lookup z corresp;;
    let '(x', corresp, av) := assign_lhs x corresp av in
    Some (corresp, av, SOp x' op y' z')
  | SSet x y =>
    y' <- lookup y corresp;;
    let '(x', corresp, av) := assign_lhs x corresp av in
    Some (corresp, av, SSet x' y')
  | SIf c s1 s2 =>
    c' <- rename_bcond corresp c;;
    (* BUG: if s1 is SSkip, the recursive call for s1 might yield registers back into av that
       are still needed in s2, so the recursive call for s2 will have the wrong corresp/av.
       On the other hand, if we made both recursive calls with the same corresp/av,
       we would have to insert phi functions at the end for vars that were assigned (to potentially
       different registers) in both branches and are used after the if *)
    '(corresp, av, s1') <- regalloc corresp av s1 l_after;;
    '(corresp, av, s2') <- regalloc corresp av s2 l_after;;
    Some (corresp, av, SIf c' s1' s2')
  | SLoop s1 c s2 =>
    '(corresp, av, s1') <- regalloc corresp av s1 (live s2 l_before);;
    c' <- rename_bcond corresp c;;
    '(corresp, av, s2') <- regalloc corresp av s2 l_before;;
    Some (corresp, av, SLoop s1' c' s2')
  | SSeq s1 s2 =>
    '(corresp, av, s1') <- regalloc corresp av s1 (live s2 l_after);;
    '(corresp, av, s2') <- regalloc corresp av s2 l_after;;
    Some (corresp, av, SSeq s1' s2')
  | SSkip =>
    Some (corresp, av, SSkip)
  | SCall binds f args =>
    args' <- lookups args corresp;;
    let '(binds', corresp, av) := assign_lhss binds corresp av in
    Some (corresp, av, SCall binds' f args')
  | SInteract binds f args =>
    args' <- lookups args corresp;;
    let '(binds', corresp, av) := assign_lhss binds corresp av in
    Some (corresp, av, SInteract binds' f args')
  end.
End WithBugs.

Definition regalloc_function: list srcvar * list srcvar * stmt -> option (list impvar * list impvar * stmt') :=
  fun '(args, rets, fbody) =>
    let corresp := process_intervals [] initial_av_regs (intervals args fbody rets) in
    fbody' <- rename corresp fbody;;
    args' <- lookups args corresp;;
    rets' <- lookups rets corresp;;
    Some (args', rets', fbody').

Scheme Equality for Syntax.access_size. (* to create access_size_beq *)
Scheme Equality for bopname. (* to create bopname_beq *)
Scheme Equality for bbinop. (* to create bbinop_beq *)

Instance access_size_beq_spec: EqDecider access_size_beq.
Proof. intros. destruct x; destruct y; simpl; constructor; congruence. Qed.

Instance bopname_beq_spec: EqDecider bopname_beq.
Proof. intros. destruct x; destruct y; simpl; constructor; congruence. Qed.

Instance bbinop_beq_spec: EqDecider bbinop_beq.
Proof. intros. destruct x; destruct y; simpl; constructor; congruence. Qed.

Section PairList.
  Context {A B: Type}.

  Definition remove_by_fst(aeqb: A -> A -> bool)(key: A): list (A * B) -> list (A * B) :=
    List.filter (fun '(a, b) => negb (aeqb a key)).

  Definition remove_by_snd(beqb: B -> B -> bool)(key: B): list (A * B) -> list (A * B) :=
    List.filter (fun '(a, b) => negb (beqb b key)).

  Lemma In_remove_by_fst{aeqb: A -> A -> bool}{aeqb_spec: EqDecider aeqb}: forall a a' b l,
      In (a, b) (remove_by_fst aeqb a' l) ->
      In (a, b) l /\ a <> a'.
  Proof.
    unfold remove_by_fst. intros. eapply filter_In in H. destruct H.
    destr (aeqb a a'). 1: discriminate. auto.
  Qed.

  Lemma not_In_remove_by_snd{beqb: B -> B -> bool}{beqb_spec: EqDecider beqb}: forall a b l,
      ~ In (a, b) (remove_by_snd beqb b l).
  Proof.
    unfold remove_by_snd, not. intros. eapply filter_In in H. apply proj2 in H.
    destr (beqb b b). 1: discriminate. apply E. reflexivity.
  Qed.

  Lemma In_remove_by_snd{beqb: B -> B -> bool}{beqb_spec: EqDecider beqb}: forall a b b' l,
      In (a, b) (remove_by_snd beqb b' l) ->
      In (a, b) l /\ b <> b'.
  Proof.
    unfold remove_by_snd. intros. eapply filter_In in H. destruct H.
    destr (beqb b b'). 1: discriminate. auto.
  Qed.
End PairList.

Section IntersectLemmas.
  Context {A: Type}(aeqb: A -> A -> bool){aeqb_spec: EqDecider aeqb}.

  Lemma intersect_max_length_l: forall l1 l2,
      (length (list_intersect aeqb l1 l2) <= length l1)%nat.
  Proof.
    intros.
    induction l1; intros.
    - simpl. reflexivity.
    - unfold list_intersect in *. cbn [fold_right]. destruct_one_match.
      + cbn [length]. eapply Peano.le_n_S. apply IHl1.
      + cbn [length]. eapply Nat.le_trans. 1: apply IHl1. constructor. reflexivity.
  Qed.

  Lemma intersect_same_length: forall l1 l2,
      length (list_intersect aeqb l1 l2) = length l1 ->
      list_intersect aeqb l1 l2 = l1.
  Proof.
    induction l1; intros.
    - reflexivity.
    - simpl in *. destruct_one_match; simpl in *.
      + f_equal. eapply IHl1. congruence.
      + pose proof (intersect_max_length_l l1 l2) as P.
        rewrite H in P. exfalso. eapply Nat.nle_succ_diag_l. exact P.
  Qed.
End IntersectLemmas.

#[export] Hint Resolve Byte.eqb_spec : typeclass_instances.

Definition assert(b: bool): option unit := if b then Some tt else None.

Definition mapping_eqb: srcvar * impvar -> srcvar * impvar -> bool :=
  fun '(x, x') '(y, y') => andb (String.eqb x y) (Z.eqb x' y').

Definition assert_in(y: srcvar)(y': impvar)(m: list (srcvar * impvar)): option unit :=
  _ <- List.find (mapping_eqb (y, y')) m;; Some tt.

Definition assert_ins(args: list srcvar)(args': list impvar)(m: list (srcvar * impvar)): option unit :=
  assert (Nat.eqb (List.length args) (List.length args'));;
  assert (List.forallb (fun p => if List.find (mapping_eqb p) m then true else false)
                       (List.combine args args')).

Definition check_bcond(m: list (srcvar * impvar))(c: bcond)(c': bcond'): option unit :=
  match c, c' with
  | CondBinary op y z, CondBinary op' y' z' =>
    assert_in y y' m;; assert_in z z' m;; assert (bbinop_beq op op')
  | CondNez y, CondNez y' =>
    assert_in y y' m
  | _, _ => None
  end.

Definition assignment(m: list (srcvar * impvar))(x: srcvar)(x': impvar): list (srcvar * impvar) :=
  (x, x') :: (remove_by_snd Z.eqb x' (remove_by_fst String.eqb x m)).

Fixpoint assignments(m: list (srcvar * impvar))(xs: list srcvar)(xs': list impvar):
  option (list (srcvar * impvar)) :=
  match xs, xs' with
  | x :: xs0, x' :: xs0' => assignments (assignment m x x') xs0 xs0'
  | nil, nil => Some m
  | _, _ => None
  end.

Section LoopInv.
  Context (check: list (srcvar * impvar) -> stmt -> stmt' -> option (list (srcvar * impvar)))
          (s1 s2: stmt)(s1' s2': stmt').

  (* Probably one iteration to compute the invariant, and another one to check that it
     doesn't change any more, ie 2 iterations, is enough, but that might be hard to prove.
     `List.length m` is enough fuel because the size can decrease at most that many times
     before we get to an empty invariant. *)
  Fixpoint loop_inv'(fuel: nat)(m: list (srcvar * impvar)): option (list (srcvar * impvar)) :=
    match fuel with
    | O => None
    | S fuel' =>
      m1 <- check m s1 s1';;
      m2 <- check m1 s2 s2';;
      let cand := list_intersect mapping_eqb m m2 in
      if Nat.eqb (List.length m) (List.length cand)
      then Some cand
      else loop_inv' fuel' cand
    end.
End LoopInv.

(* does 2 things at once: checks that the correct variables are read and computes the bindings
   that hold after executing the statement *)
(* m: conservative underapproximation of which impvar stores which srcvar *)
Fixpoint check(m: list (srcvar * impvar))(s: stmt)(s': stmt'){struct s}: option (list (srcvar * impvar)) :=
  match s, s' with
  | SLoad sz x y ofs, SLoad sz' x' y' ofs' =>
    assert_in y y' m;;
    assert (Z.eqb ofs ofs');;
    assert (access_size_beq sz sz');;
    Some (assignment m x x')
  | SStore sz x y ofs, SStore sz' x' y' ofs' =>
    assert_in x x' m;;
    assert_in y y' m;;
    assert (Z.eqb ofs ofs');;
    assert (access_size_beq sz sz');;
    Some m
  | SInlinetable sz x bs y, SInlinetable sz' x' bs' y' =>
    assert_in y y' m;;
    (* FlatToRiscv uses x' as a tmp register, and that should not overwrite y' *)
    assert (negb (Z.eqb x' y'));;
    assert (access_size_beq sz sz');;
    assert (List.list_eqb Byte.eqb bs bs');;
    Some (assignment m x x')
  | SStackalloc x n body, SStackalloc x' n' body' =>
    assert (Z.eqb n n');;
    check (assignment m x x') body body'
  | SLit x z, SLit x' z' =>
    assert (Z.eqb z z');;
    Some (assignment m x x')
  | SOp x op y z, SOp x' op' y' z' =>
    assert_in y y' m;;
    assert_in z z' m;;
    assert (bopname_beq op op');;
    Some (assignment m x x')
  | SSet x y, SSet x' y' =>
    assert_in y y' m;; Some (assignment m x x')
  | SIf c s1 s2, SIf c' s1' s2' =>
    check_bcond m c c';;
    m1 <- check m s1 s1';;
    m2 <- check m s2 s2';;
    Some (list_intersect mapping_eqb m1 m2)
  | SLoop s1 c s2, SLoop s1' c' s2' =>
    inv <- loop_inv' check s1 s2 s1' s2' (S (List.length m)) m;;
    m1 <- check inv s1 s1';;
    check_bcond m1 c c';;
    m2 <- check m1 s2 s2';;
    Some m1
  | SSeq s1 s2, SSeq s1' s2' =>
    m1 <- check m s1 s1';;
    check m1 s2 s2'
  | SSkip, SSkip =>
    Some m
  | SCall binds f args, SCall binds' f' args'
  | SInteract binds f args, SInteract binds' f' args' =>
    assert (String.eqb f f');;
    assert_ins args args' m;;
    assignments m binds binds'
  | _, _ => None
  end.

Definition check_func: list srcvar * list srcvar * stmt -> list impvar * list impvar * stmt' -> option unit :=
  fun '(args, rets, body) '(args', rets', body') =>
    assert (List.list_eqb Z.eqb (List.dedup Z.eqb args') args');;
    assert (List.list_eqb Z.eqb (List.dedup Z.eqb rets') rets');;
    m0 <- assignments [] args args';;
    m1 <- check m0 body body';;
    assert_ins rets rets' m1.

Section WithEnv.
  Context {srcEnv: map.map String.string (list srcvar * list srcvar * stmt)}.
  Context {impEnv: map.map String.string (list impvar * list impvar * stmt')}.

  Definition lookup_and_check_func(e': impEnv)(fname: String.string)(impl: list srcvar * list srcvar * stmt) :=
    match map.get e' fname with
    | Some impl' => if check_func impl impl' then true else false
    | None => false
    end.

  Definition check_funcs(e: srcEnv)(e': impEnv): bool :=
    map.forallb (lookup_and_check_func e') e.

  Definition regalloc_functions(e: srcEnv): option impEnv :=
    e' <- map.map_all_values regalloc_function e;;
    if check_funcs e e' then Some e' else None.
End WithEnv.

Definition loop_inv(corresp: list (srcvar * impvar))(s1 s2: stmt)(s1' s2': stmt'): list (srcvar * impvar) :=
  match loop_inv' check s1 s2 s1' s2' (S (List.length corresp)) corresp with
  | Some inv => inv
  | None => []
  end.

Definition extends(m1 m2: list (srcvar * impvar)): Prop :=
  forall x x', assert_in x x' m2 = Some tt -> assert_in x x' m1 = Some tt.

Lemma extends_refl: forall m, extends m m.
Proof. unfold extends. eauto. Qed.

Lemma extends_nil: forall m, extends m [].
Proof. unfold extends, assert_in. simpl. intros. discriminate. Qed.

Lemma extends_trans: forall m1 m2 m3, extends m1 m2 -> extends m2 m3 -> extends m1 m3.
Proof. unfold extends. eauto. Qed.

Lemma extends_cons: forall a l1 l2,
    extends l1 l2 ->
    extends (a :: l1) (a :: l2).
Proof.
  unfold extends, assert_in. simpl. intros. simp.
  destruct_one_match_hyp. 1: reflexivity.
  eapply H. rewrite E. reflexivity.
Qed.

Lemma extends_cons_l: forall a l,
    extends (a :: l) l.
Proof.
  unfold extends, assert_in. simpl. intros. simp.
  destruct_one_match. 1: reflexivity.
  destruct_one_match_hyp; discriminate.
Qed.

Lemma extends_cons_r: forall a l1 l2,
    In a l1 ->
    extends l1 l2 ->
    extends l1 (a :: l2).
Proof.
  unfold extends, assert_in. simpl. intros. simp.
  destruct_one_match_hyp. 2: {
    eapply H0. rewrite E. reflexivity.
  }
  destruct_one_match. 1: reflexivity.
  eapply find_none in E1. 2: eassumption.
  simpl in E1. exfalso. congruence.
Qed.

Lemma extends_intersect_l: forall l1 l2,
    extends l1 (list_intersect mapping_eqb l1 l2).
Proof.
  intros. induction l1; simpl.
  - apply extends_refl.
  - destruct_one_match.
    + eapply extends_cons. apply IHl1.
    + eapply extends_trans. 2: apply IHl1. apply extends_cons_l.
Qed.

Lemma extends_intersect_r: forall l1 l2,
    extends l2 (list_intersect mapping_eqb l1 l2).
Proof.
  induction l1; intros.
  - simpl. apply extends_nil.
  - simpl. unfold mapping_eqb. destruct a as [x x']. destruct_one_match.
    + destruct p as [z z']. eapply find_some in E. destruct E as [E1 E2].
      apply Bool.andb_true_iff in E2. destruct E2 as [E2 E3].
      autoforward with typeclass_instances in E2.
      autoforward with typeclass_instances in E3.
      subst z z'.
      eapply extends_cons_r. 1: assumption. apply IHl1.
    + apply IHl1.
Qed.

Lemma extends_loop_inv': forall s1 s2 s1' s2' fuel corresp1 corresp2,
    loop_inv' check s1 s2 s1' s2' fuel corresp1 = Some corresp2 ->
    extends corresp1 corresp2.
Proof.
  induction fuel; simpl; intros.
  - discriminate.
  - simp. destruct_one_match_hyp.
    + simp. symmetry in E1. eapply intersect_same_length in E1.
      rewrite E1. eapply extends_refl.
    + eapply IHfuel in H. eapply extends_trans.
      2: exact H. apply extends_intersect_l.
Qed.

Lemma extends_loop_inv: forall corresp s1 s2 s1' s2',
    extends corresp (loop_inv corresp s1 s2 s1' s2').
Proof.
  intros. unfold loop_inv. destruct_one_match. 2: {
    unfold extends. unfold assert_in. simpl. intros. discriminate.
  }
  eapply extends_loop_inv'. eassumption.
Qed.

Lemma defuel_loop_inv': forall fuel corresp inv m1 m2 s1 s2 s1' s2',
    loop_inv' check s1 s2 s1' s2' fuel corresp = Some inv ->
    check inv s1 s1' = Some m1 ->
    check m1 s2 s2' = Some m2 ->
    inv = list_intersect mapping_eqb inv m2.
Proof.
  induction fuel; intros; simpl in *.
  - discriminate.
  - simp. destruct_one_match_hyp.
    + simp. symmetry in E1. eapply intersect_same_length in E1. rewrite E1 in H0.
      rewrite E in H0. simp.
      rewrite E0 in H1. simp.
      rewrite <- E1 at 1. reflexivity.
    + eapply IHfuel; eassumption.
Qed.

(* Similar effect as unfolding loop_inv where loop_inv's definition does not involve fuel,
   ie this lemma allows us to prove `inv = intersect inv (update inv loop_body)` *)
Lemma defuel_loop_inv: forall corresp inv m1 m2 s1 s2 s1' s2',
    inv = loop_inv corresp s1 s2 s1' s2' ->
    check inv s1 s1' = Some m1 ->
    check m1 s2 s2' = Some m2 ->
    inv = list_intersect mapping_eqb inv m2.
Proof.
  unfold loop_inv. intros. subst. destruct_one_match. 2: reflexivity.
  eapply defuel_loop_inv'; eassumption.
Qed.

Section RegAlloc.

  Context {width} {BW: Bitwidth width} {word: word.word width} {word_ok: word.ok word}.
  Context {mem: map.map word byte}.
  Context {srcLocals: map.map srcvar word}.
  Context {impLocals: map.map impvar word}.
  Context {srcLocalsOk: map.ok srcLocals}.
  Context {impLocalsOk: map.ok impLocals}.
  Context {srcEnv: map.map String.string (list srcvar * list srcvar * stmt)} {srcEnvOk: map.ok srcEnv}.
  Context {impEnv: map.map String.string (list impvar * list impvar * stmt')} {impEnvOk: map.ok impEnv}.
  Context {ext_spec: Semantics.ExtSpec}.

  Definition states_compat(st: srcLocals)(corresp: list (srcvar * impvar))(st': impLocals) :=
    forall (x: srcvar) (x': impvar),
      assert_in x x' corresp = Some tt ->
      forall w,
        map.get st x = Some w ->
        map.get st' x' = Some w.

  Definition precond(corresp: list (srcvar * impvar))(s: stmt)(s': stmt'): list (srcvar * impvar) :=
    match s, s' with
    | SLoop s1 c s2, SLoop s1' c' s2' => loop_inv corresp s1 s2 s1' s2'
    | _, _ => corresp
    end.

  Lemma states_compat_eval_bcond: forall lH lL c c' b corresp,
      check_bcond corresp c c' = Some tt ->
      eval_bcond lH c = Some b ->
      states_compat lH corresp lL ->
      eval_bcond lL c' = Some b.
  Proof.
    intros. rename H1 into C. unfold states_compat in C.
    destruct c; cbn in *; simp;
      repeat match goal with
             | u: unit |- _ => destruct u
             end;
      unfold assert in *;
      cbn; simp;
      repeat match goal with
             | H: @eq bool _ _ |- _ => autoforward with typeclass_instances in H
             end;
      subst;
      erewrite ?C by eauto; reflexivity.
  Qed.

  Lemma states_compat_eval_bcond_None: forall lH lL c c' corresp,
      check_bcond corresp c c' = Some tt ->
      eval_bcond lH c <> None ->
      states_compat lH corresp lL ->
      eval_bcond lL c' <> None.
  Proof.
    intros. destr (eval_bcond lH c). 2: congruence.
    erewrite states_compat_eval_bcond; eassumption.
  Qed.

  Lemma states_compat_eval_bcond_bw: forall lH lL c c' b corresp,
      check_bcond corresp c c' = Some tt ->
      eval_bcond lL c' = Some b ->
      states_compat lH corresp lL ->
      eval_bcond lH c <> None ->
      eval_bcond lH c = Some b.
  Proof.
    intros. destr (eval_bcond lH c). 2: congruence.
    symmetry. rewrite <- H0. eapply states_compat_eval_bcond; eassumption.
  Qed.

  Lemma states_compat_empty: forall corresp lL,
      states_compat map.empty corresp lL.
  Proof. unfold states_compat. intros. rewrite map.get_empty in H0. discriminate. Qed.

  Lemma states_compat_extends: forall lH m1 m2 lL,
      extends m1 m2 ->
      states_compat lH m1 lL ->
      states_compat lH m2 lL.
  Proof.
    unfold states_compat, extends. intros. eauto.
  Qed.

  Lemma states_compat_precond: forall lH corresp lL s s',
      states_compat lH corresp lL ->
      states_compat lH (precond corresp s s') lL.
  Proof.
    intros.
    destruct s; cbn; try assumption.
    destruct s'; cbn; try assumption.
    eapply states_compat_extends. 2: eassumption.
    eapply extends_loop_inv.
  Qed.
  Hint Resolve states_compat_precond : states_compat.

  Lemma states_compat_get: forall corresp lL lH y y' v,
      states_compat lH corresp lL ->
      assert_in y y' corresp = Some tt ->
      map.get lH y = Some v ->
      map.get lL y' = Some v.
  Proof. unfold states_compat. eauto. Qed.

  Lemma states_compat_getmany: forall corresp lL lH ys ys' vs,
      states_compat lH corresp lL ->
      assert_ins ys ys' corresp = Some tt ->
      map.getmany_of_list lH ys = Some vs ->
      map.getmany_of_list lL ys' = Some vs.
  Proof.
    induction ys; intros.
    - unfold assert_ins in *. cbn in *. simp. destruct ys'. 2: discriminate. reflexivity.
    - cbn in *. unfold assert_ins, assert in H0. simp.
      autoforward with typeclass_instances in E3. destruct ys' as [|a' ys']. 1: discriminate.
      inversion E3. clear E3.
      cbn in *. simp. simpl in E2.
      erewrite states_compat_get; try eassumption. 2: {
        unfold assert_in. unfold mapping_eqb. rewrite E1. reflexivity.
      }
      unfold map.getmany_of_list in *.
      erewrite IHys; eauto.
      unfold assert_ins. rewrite H1. rewrite Nat.eqb_refl. simpl.
      unfold assert. rewrite E2. reflexivity.
  Qed.

  Lemma states_compat_put: forall lH corresp lL x x' v,
      states_compat lH corresp lL ->
      states_compat (map.put lH x v) (assignment corresp x x') (map.put lL x' v).
  Proof.
    intros. unfold states_compat in *. intros k k'. intros.
    rewrite map.get_put_dec. rewrite map.get_put_dec in H1.
    unfold assert_in, assignment in H0. simp. simpl in E.
    rewrite String.eqb_sym, Z.eqb_sym in E.
    destr (Z.eqb x' k').
    - subst k'.
      destr (String.eqb x k).
      + assumption.
      + simpl in E. eapply find_some in E. destruct E as [E F].
        destruct p. eapply Bool.andb_true_iff in F. destruct F as [F1 F2].
        eapply String.eqb_eq in F1. subst s.
        eapply Z.eqb_eq in F2. subst z.
        exfalso. eapply not_In_remove_by_snd in E. exact E.
    - rewrite Bool.andb_false_r in E.
      eapply find_some in E. destruct E as [E F].
      destruct p. eapply Bool.andb_true_iff in F. destruct F as [F1 F2].
      eapply String.eqb_eq in F1. subst s.
      eapply Z.eqb_eq in F2. subst z.
      eapply In_remove_by_snd in E. apply proj1 in E.
      eapply In_remove_by_fst in E. destruct E.
      destr (String.eqb x k).
      + exfalso. congruence.
      + eapply H. 2: eassumption. unfold assert_in.
        destruct_one_match. 1: reflexivity.
        eapply find_none in E1. 2: eassumption.
        simpl in E1. rewrite String.eqb_refl, Z.eqb_refl in E1. discriminate.
  Qed.

  Lemma putmany_of_list_zip_states_compat: forall binds binds' resvals lL lH l' corresp corresp',
      map.putmany_of_list_zip binds resvals lH = Some l' ->
      assignments corresp binds binds' = Some corresp' ->
      states_compat lH corresp lL ->
      exists lL',
        map.putmany_of_list_zip binds' resvals lL = Some lL' /\
        states_compat l' corresp' lL'.
  Proof.
    induction binds; intros.
    - simpl in H. simp. destruct binds'. 2: discriminate.
      simpl in *. simp. eauto.
    - simpl in *. simp.
      specialize IHbinds with (1 := H).
      rename l' into lH'.
      edestruct IHbinds as (lL' & P & C). 1: eassumption. 1: eapply states_compat_put. 1: eassumption.
      simpl. rewrite P. eauto.
  Qed.

  Lemma assignments_same_length: forall xs xs' m1 m2,
      assignments m1 xs xs' = Some m2 -> List.length xs = List.length xs'.
  Proof.
    induction xs; intros; destruct xs'; try discriminate.
    - reflexivity.
    - simpl in *. f_equal. eapply IHxs. eassumption.
  Qed.

  Lemma assert_ins_same_length: forall xs xs' m u,
      assert_ins xs xs' m = Some u -> List.length xs = List.length xs'.
  Proof.
    unfold assert_ins, assert. intros. simp. apply Nat.eqb_eq. assumption.
  Qed.

  Hint Constructors exec.exec : checker_hints.
  Hint Resolve states_compat_get : checker_hints.
  Hint Resolve states_compat_put : checker_hints.

  Lemma checker_correct: forall (e: srcEnv) (e': impEnv) s t m lH mc post,
      check_funcs e e' = true ->
      exec e s t m lH mc post ->
      forall lL corresp corresp' s',
      check corresp s s' = Some corresp' ->
      states_compat lH (precond corresp s s') lL ->
      exec e' s' t m lL mc (fun t' m' lL' mc' =>
        exists lH', states_compat lH' corresp' lL' /\ post t' m' lH' mc').
  Proof.
    induction 2; intros;
      match goal with
      | H: check _ _ _ = Some _ |- _ => pose proof H as C; move C at top; cbn [check] in H
      end;
      simp;
      repeat match goal with
             | u: unit |- _ => destruct u
             end;
      unfold assert in *;
      simp;
      repeat match goal with
             | H: negb _ = false |- _ => apply Bool.negb_false_iff in H
             | H: negb _ = true  |- _ => apply Bool.negb_true_iff in H
             | H: @eq bool _ _ |- _ => autoforward with typeclass_instances in H
             end;
      subst;
      cbn [precond] in *.

    - (* Case exec.interact *)
      eapply exec.interact; eauto using states_compat_getmany.
      intros. edestruct H3 as (l' & P & F). 1: eassumption.
      eapply putmany_of_list_zip_states_compat in P. 2-3: eassumption. destruct P as (lL' & P & SC).
      eexists. split. 1: eassumption. intros. eauto.
    - (* Case exec.call *)
      rename binds0 into binds', args0 into args'.
      unfold check_funcs in H.
      eapply map.get_forallb in H. 2: eassumption.
      unfold lookup_and_check_func in *. simp.
      destruct p as ((params' & rets') & fbody').
      unfold check_func in *. simp.
      apply_in_hyps @map.getmany_of_list_length.
      apply_in_hyps assert_ins_same_length.
      apply_in_hyps assignments_same_length.
      apply_in_hyps @map.putmany_of_list_zip_sameLength.
      assert (length params' = length argvs) as L3 by congruence.
      eapply map.sameLength_putmany_of_list in L3. destruct L3 as [lLF' L3].
      eapply @exec.call. 1: eassumption. 1: eauto using states_compat_getmany. 1: exact L3.
      + eapply IHexec. 1: eassumption. eapply states_compat_precond.
        edestruct putmany_of_list_zip_states_compat as [ lLF0 [L SC] ].
        2: exact E4. 2: eapply states_compat_empty. 1: eassumption.
        rewrite L3 in L. apply Option.eq_of_eq_Some in L. subst lLF0. exact SC.
      + cbv beta. intros. simp. edestruct H4 as (retvs & lHF' & G & P & Hpost). 1: eassumption.
        edestruct putmany_of_list_zip_states_compat as (lL' & L4 & SC).
        1: exact P. 1: exact H5. 1: eassumption.
        destruct u.
        do 2 eexists. ssplit.
        * eapply states_compat_getmany; eassumption.
        * exact L4.
        * eexists. split. 2: eassumption. exact SC.
    - (* Case exec.load *)
      eauto 10 with checker_hints.
    - (* Case exec.store *)
      eauto 10 with checker_hints.
    - (* Case exec.inlinetable *)
      eauto 10 with checker_hints.
    - (* Case exec.stackalloc *)
      eapply exec.stackalloc. 1: assumption.
      intros. eapply exec.weaken.
      + eapply H2; try eassumption.
        eapply states_compat_precond. eapply states_compat_put. assumption.
      + cbv beta. intros. simp. eauto 10 with checker_hints.
    - (* Case exec.lit *)
      eauto 10 with checker_hints.
    - (* Case exec.op *)
      eauto 10 with checker_hints.
    - (* Case exec.set *)
      eauto 10 with checker_hints.
    - (* Case exec.if_true *)
      eapply exec.if_true. 1: eauto using states_compat_eval_bcond.
      eapply exec.weaken.
      + eapply IHexec. 1: eassumption.
        eapply states_compat_precond. eassumption.
      + cbv beta. intros. simp. eexists. split. 2: eassumption.
        eapply states_compat_extends. 2: eassumption. eapply extends_intersect_l.
    - (* Case exec.if_false *)
      eapply exec.if_false. 1: eauto using states_compat_eval_bcond.
      eapply exec.weaken.
      + eapply IHexec. 1: eassumption.
        eapply states_compat_precond. eassumption.
      + cbv beta. intros. simp. eexists. split. 2: eassumption.
        eapply states_compat_extends. 2: eassumption. eapply extends_intersect_r.
    - (* Case exec.loop *)
      rename H4 into IH2, IHexec into IH1, H6 into IH12.
      match goal with
      | H: states_compat _ _ _ |- _ => rename H into SC
      end.
      pose proof SC as SC0.
      unfold loop_inv in SC.
      rewrite E in SC.
      eapply exec.loop.
      + eapply IH1. 1: eassumption. eapply states_compat_precond. exact SC.
      + cbv beta. intros. simp. eauto using states_compat_eval_bcond_None.
      + cbv beta. intros. simp. eexists. split. 2: eauto using states_compat_eval_bcond_bw. assumption.
      + cbv beta. intros. simp. eapply IH2; eauto using states_compat_eval_bcond_bw.
        eapply states_compat_precond. assumption.
      + cbv beta. intros. simp. eapply IH12. 1: eassumption. 1: eassumption.
        rename l0 into inv.
        eapply states_compat_extends. 2: eassumption.
        pose proof defuel_loop_inv as P.
        specialize P with (2 := E0).
        specialize P with (2 := E2).
        specialize (P corresp).
        unfold loop_inv in P|-*.
        rewrite E in P. rewrite E.
        specialize (P eq_refl).
        rewrite P.
        eapply extends_intersect_r.
    - (* Case exec.seq *)
      rename H2 into IH2, IHexec into IH1.
      eapply exec.seq.
      + eapply IH1. 1: eassumption.
        eapply states_compat_precond. assumption.
      + cbv beta. intros. simp.
        eapply IH2. 1: eassumption. 1: eassumption.
        eapply states_compat_precond. assumption.
    - (* Case exec.skip *)
      eapply exec.skip. eauto.
  Qed.

End RegAlloc.
