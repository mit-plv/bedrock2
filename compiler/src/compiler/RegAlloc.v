Require Import compiler.util.Common.
Require Import bedrock2.LeakageSemantics.
Require Import compiler.FlatImp.
Require Import coqutil.Tactics.simpl_rewrite.
Require Import Coq.Lists.List. Import ListNotations.
Require Import riscv.Utility.Utility.
Require Import coqutil.Map.MapEauto.
Require Import bedrock2.Syntax.
Require Import coqutil.Datatypes.ListSet.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Tactics.autoforward.
Require Import compiler.Registers.
Require Import bedrock2.MetricLogging.
Require Import bedrock2.MetricCosts.

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

  | SOp x _ y z => let var_z := match z with
                                | Var vz => [vz]
                                | Const _ => []
                                end in
                   list_union String.eqb ([y] ++ var_z) (list_diff String.eqb used_after [x])
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
  | SOp x _ y z => end_event y ++ (match z with
                                   | Const cz => []
                                   | Var vz => end_event vz
                                   end) ++ start_event x ++ after
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
  let arg_start_events := List.flat_map start_event input_vars in
  (* We duplicate the arg_start_events (of which each also includes an end event) to
     make sure that all argument variables seem live at the same time, so that
     argument variables don't get assigned to the same registers, even if they are
     never read *)
  let unfiltered := arg_start_events ++ arg_start_events ++
                    (events s (List.flat_map end_event output_vars)) in
  remove_nonfirst_starts [] (remove_nonlast_ends unfiltered).

(* TODO: once spilling is changed, this will change too *)
Definition not_reserved(x: Z): bool := 5 <? x.

Definition temp_regs : list impvar := Eval compute in List.filter not_reserved (reg_class.all reg_class.temp).
Definition saved_regs: list impvar := Eval compute in List.filter not_reserved (reg_class.all reg_class.saved).
Definition arg_regs  : list impvar := Eval compute in List.filter not_reserved (reg_class.all reg_class.arg).


(* ** Previous implementation: assign impvars in one scan over the events *)

(* Register availability, split by how preferable they are.
   For simplicity, we use the argument registers *only* for argument passing and as spilling temporaries. *)
Record av_regs: Set := mk_av_regs {
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

Definition lookup(x: srcvar)(corresp: list (srcvar * impvar)): result impvar :=
  match List.find (fun p => String.eqb x (fst p)) corresp with
  | Some (_, x') => Success x'
  | None => error:(x "not found")
  end.

Definition lookups(xs: list srcvar)(corresp: list (srcvar * impvar)): result (list impvar) :=
  List.all_success (List.map (fun arg => lookup arg corresp) xs).

Fixpoint process_intervals(corresp: list (srcvar * impvar))(av: av_regs)(l: list event):
  list (srcvar * impvar) :=
  match l with
  | (x, is_start) :: rest =>
    if is_start then
      let (y, av) := acquire_reg av in process_intervals ((x, y) :: corresp) av rest
    else
      let av := match lookup x corresp with
                | Success y => yield_reg y av
                | Failure _ => av (* unexpected: end_event without start_event *)
                end in
      process_intervals corresp av rest
  | nil => corresp
  end.


(* ** New implementation: Process source variables from shortest to longest lifetime *)

(* varname, start time, live interval length *)
Definition lifetime := (string * (Z * Z))%type.

Definition non_overlapping: lifetime -> lifetime -> bool :=
  fun '(_, (start1, len1)) '(_, (start2, len2)) =>
    if start1 + len1 <? start2 then true else start2 + len2 <? start1.

(* custom implementation because List.forallb is not short-circuiting *)
Section ConflictFree.
  Context (candidate: lifetime).
  Fixpoint conflict_free(occ: list lifetime): bool :=
    match occ with
    | nil => true
    | l :: tail => if non_overlapping candidate l then conflict_free tail else false
    end.
End ConflictFree.

(* i-th element contains list of intervals during which i-th impvar is occupied *)
Definition occupancy := list (list lifetime).

Fixpoint assign_srcvar(occs: occupancy)(v: lifetime): occupancy :=
  match occs with
  | occ :: tail => if conflict_free v occ then ((v :: occ) :: tail)
                   else occ :: assign_srcvar tail v
  | nil => [ [v] ] (* start using next (so far unused) register or stack slot *)
  end.

Section Sorting.
  Context {A: Type} (lt: A -> A -> bool).

  Section WithA.
    Context (a: A).
    Fixpoint insert_into_sorted(l: list A): list A :=
      match l with
      | [] => [a]
      | h :: t => if lt a h then a :: l else h :: (insert_into_sorted t)
      end.
  End WithA.

  Definition sort: list A -> list A := List.fold_right insert_into_sorted nil.
End Sorting.

Definition compare_interval_length: lifetime -> lifetime -> bool :=
  fun '(name1, (start1, len1)) '(name2, (start2, len2)) => Z.ltb len1 len2.

Section IndexOf.
  Context {A: Type} (predicate: A -> bool).
  Fixpoint index_of(l: list A): Z :=
    match l with
    | [] => -1
    | h :: t => if predicate h then 0 else
                  let rec := index_of t in
                  match rec with
                  | Zneg _ => rec
                  | _ => rec + 1
                  end
    end.
End IndexOf.

Goal index_of (Z.eqb 3) [4; 3; 1] = 1. cbv. reflexivity. Abort.
Goal index_of (Z.eqb 3) [4; 4; 1] = -1. cbv. reflexivity. Abort.

Fixpoint events_to_intervals(current_time: Z)(events: list event): list lifetime :=
  match events with
  | (varname, is_start) :: tail =>
      let rec := events_to_intervals (current_time + 1) tail in
      if is_start then
        let len := 1 + index_of (fun '(varname', _) => String.eqb varname varname') tail in
        (varname, (current_time, len)) :: rec
      else rec
  | nil => nil
  end.

(* We use registers x6 to x9, registers x18 to x31, and stack slots x32 and beyond *)
Definition first_available_impvar := 6.
Definition next_available_impvar(v: Z): Z :=
  if Z.eqb v 9 then 18 else v + 1.

Fixpoint add_corresp_of_impvar(impvarname: Z)(occ: list lifetime)
  (corresp: list (srcvar * impvar)): list (srcvar * impvar) :=
  match occ with
  | (srcvarname, _) :: tail =>
      (srcvarname, impvarname) :: add_corresp_of_impvar impvarname tail corresp
  | nil => corresp
  end.

Fixpoint corresp_of_impvars(start_impvar: Z)(o: occupancy): list (srcvar * impvar) :=
  match o with
  | h :: t => add_corresp_of_impvar start_impvar h
                (corresp_of_impvars (next_available_impvar start_impvar) t)
  | nil => nil
  end.

Definition events_to_corresp(events: list event): list (srcvar * impvar) :=
  let sorted_intervals := sort compare_interval_length (events_to_intervals 0 events) in
  let occ := List.fold_left assign_srcvar sorted_intervals [] in
  corresp_of_impvars first_available_impvar occ.


(* ** Common: Applying a rename mapping (corresp) *)

Definition rename_bcond(corresp: list (srcvar * impvar))(c: bcond): result bcond' :=
  match c with
  | CondBinary op y z =>
    y' <- lookup y corresp;;
    z' <- lookup z corresp;;
    Success (CondBinary op y' z')
  | CondNez y =>
    y' <- lookup y corresp;;
    Success (CondNez y')
  end.

Definition lookup_op_corresp (op: @operand srcvar) (corresp: list (srcvar * impvar)): result (@operand impvar)  :=
  match op with
  | Const cp => Success (Const cp)
  | Var vp  => (lp <- lookup vp corresp;; Success (Var lp))
  end.

Fixpoint rename(corresp: list (srcvar * impvar))(s: stmt): result stmt' :=
  match s with
  | SLoad sz x y ofs =>
    x' <- lookup x corresp;;
    y' <- lookup y corresp;;
    Success (SLoad sz x' y' ofs)
  | SStore sz x y ofs =>
    x' <- lookup x corresp;;
    y' <- lookup y corresp;;
    Success (SStore sz x' y' ofs)
  | SInlinetable sz x bs y =>
    x' <- lookup x corresp;;
    y' <- lookup y corresp;;
    Success (SInlinetable sz x' bs y')
  | SStackalloc x n body =>
    x' <- lookup x corresp;;
    body' <- rename corresp body;;
    Success (SStackalloc x' n body')
  | SLit x z =>
    x' <- lookup x corresp;;
    Success (SLit x' z)
  | SOp x op y z =>
    x' <- lookup x corresp;;
    y' <- lookup y corresp;;
    z' <- lookup_op_corresp z corresp;;
    Success (SOp x' op y' z')
  | SSet x y =>
    x' <- lookup x corresp;;
    y' <- lookup y corresp;;
    Success (SSet x' y')
  | SIf c s1 s2 =>
    c' <- rename_bcond corresp c;;
    s1' <- rename corresp s1;;
    s2' <- rename corresp s2;;
    Success (SIf c' s1' s2')
  | SLoop s1 c s2 =>
    s1' <- rename corresp s1;;
    c' <- rename_bcond corresp c;;
    s2' <- rename corresp s2;;
    Success (SLoop s1' c' s2')
  | SSeq s1 s2 =>
    s1' <- rename corresp s1;;
    s2' <- rename corresp s2;;
    Success (SSeq s1' s2')
  | SSkip =>
    Success SSkip
  | SCall binds f args =>
    args' <- lookups args corresp;;
    binds' <- lookups binds corresp;;
    Success (SCall binds' f args')
  | SInteract binds f args =>
    args' <- lookups args corresp;;
    binds' <- lookups binds corresp;;
    Success (SInteract binds' f args')
  end.

Module WithBugs.
Definition assign_lhs(x: srcvar)(corresp: list (srcvar * impvar))(av: av_regs) :=
  match lookup x corresp with
  | Success x' => (x', corresp, av)
  | Failure _ => let '(x', av) := acquire_reg av in (x', (x, x') :: corresp, av)
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
  result (list (srcvar * impvar) * av_regs * stmt') := (* should aways return Success *)
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
    Success (corresp, av, SLoad sz x' y' ofs)
  | SStore sz x y ofs =>
    x' <- lookup x corresp;;
    y' <- lookup y corresp;;
    Success (corresp, av, SStore sz x' y' ofs)
  | SInlinetable sz x bs y =>
    (* Note: We expect that x<>y and that the srcvar->impvar mapping in corresp is injective,
       so we get x'<>y', which is required by exec.inlinetable *)
    y' <- lookup y corresp;;
    let '(x', corresp, av) := assign_lhs x corresp av in
    Success (corresp, av, SInlinetable sz x' bs y')
  | SStackalloc x n body =>
    let '(x', corresp, av) := assign_lhs x corresp av in
    '(corresp, av, body') <- regalloc corresp av body l_after;;
    Success (corresp, av, SStackalloc x' n body')
  | SLit x z =>
    let '(x', corresp, av) := assign_lhs x corresp av in
    Success (corresp, av, SLit x' z)
  | SOp x op y z =>
    y' <- lookup y corresp;;
    z' <- lookup_op_corresp z corresp;;
    let '(x', corresp, av) := assign_lhs x corresp av in
    Success (corresp, av, SOp x' op y' z')
  | SSet x y =>
    y' <- lookup y corresp;;
    let '(x', corresp, av) := assign_lhs x corresp av in
    Success (corresp, av, SSet x' y')
  | SIf c s1 s2 =>
    c' <- rename_bcond corresp c;;
    (* BUG: if s1 is SSkip, the recursive call for s1 might yield registers back into av that
       are still needed in s2, so the recursive call for s2 will have the wrong corresp/av.
       On the other hand, if we made both recursive calls with the same corresp/av,
       we would have to insert phi functions at the end for vars that were assigned (to potentially
       different registers) in both branches and are used after the if *)
    '(corresp, av, s1') <- regalloc corresp av s1 l_after;;
    '(corresp, av, s2') <- regalloc corresp av s2 l_after;;
    Success (corresp, av, SIf c' s1' s2')
  | SLoop s1 c s2 =>
    '(corresp, av, s1') <- regalloc corresp av s1 (live s2 l_before);;
    c' <- rename_bcond corresp c;;
    '(corresp, av, s2') <- regalloc corresp av s2 l_before;;
    Success (corresp, av, SLoop s1' c' s2')
  | SSeq s1 s2 =>
    '(corresp, av, s1') <- regalloc corresp av s1 (live s2 l_after);;
    '(corresp, av, s2') <- regalloc corresp av s2 l_after;;
    Success (corresp, av, SSeq s1' s2')
  | SSkip =>
    Success (corresp, av, SSkip)
  | SCall binds f args =>
    args' <- lookups args corresp;;
    let '(binds', corresp, av) := assign_lhss binds corresp av in
    Success (corresp, av, SCall binds' f args')
  | SInteract binds f args =>
    args' <- lookups args corresp;;
    let '(binds', corresp, av) := assign_lhss binds corresp av in
    Success (corresp, av, SInteract binds' f args')
  end.
End WithBugs.

Definition regalloc_function: list srcvar * list srcvar * stmt -> result (list impvar * list impvar * stmt') :=
  fun '(args, rets, fbody) =>
  (*let corresp := process_intervals [] initial_av_regs (intervals args fbody rets) in*)
    let corresp := events_to_corresp (intervals args fbody rets) in
    fbody' <- rename corresp fbody;;
    args' <- lookups args corresp;;
    rets' <- lookups rets corresp;;
    Success (args', rets', fbody').

Scheme Equality for Syntax.access_size. (* to create access_size_beq *)
Scheme Equality for bopname. (* to create bopname_beq *)
Scheme Equality for bbinop. (* to create bbinop_beq *)

#[global] Instance access_size_beq_spec: EqDecider access_size_beq.
Proof. intros. destruct x; destruct y; simpl; constructor; congruence. Qed.

#[global] Instance bopname_beq_spec: EqDecider bopname_beq.
Proof. intros. destruct x; destruct y; simpl; constructor; congruence. Qed.

#[global] Instance bbinop_beq_spec: EqDecider bbinop_beq.
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

Definition assert(b: bool)(els: result unit): result unit := if b then Success tt else els.

Definition mapping_eqb: srcvar * impvar -> srcvar * impvar -> bool :=
  fun '(x, x') '(y, y') => andb (String.eqb x y) (Z.eqb x' y').

Definition check_regs (x: srcvar) (x': impvar) : bool :=
  negb (andb (isRegStr x) (negb (isRegZ x'))).

Definition check_regs_op (x: @operand srcvar) (x': @operand impvar) : bool :=
  match x, x' with
  | Var vx, Var vx' => check_regs vx vx'
  | Const cx, Const cx' => Z.eqb cx cx'
  | _, _ => false
  end.

Definition assert_in(y: srcvar)(y': impvar)(m: list (srcvar * impvar)): result unit :=
  match List.find (mapping_eqb (y, y')) m with
  | Some _ => if check_regs y y' then Success tt else
               error:("The register allocator found a mapping of source register variable" y
                      "to target stack variable" y'
                      "but source register variables must be in registers in the target.")
  | None => error:("The register allocator replaced source variable" y
                   "by target variable" y'
                   "but when the checker encountered this pair,"
                   "its current mapping of source to target variables" m
                   "did not contain the pair" (y, y'))
  end.

Definition assert_in_op (y: @operand srcvar) (y': @operand impvar) (m: list (srcvar * impvar)): result unit :=
  match y' with
  | Var vy' => match y with
               | Var vy => assert_in vy vy' m
               | Const cy => error:("The register allocator replaced source constant" cy
                                    "by target variable" vy')
               end
  | Const cy' => match y with
                 | Var vy => error:("The register allocator replaced source variable" vy
                                      "by target constant" cy')
                 | Const cy => match Z.eqb cy cy' with
                               | true => Success tt
                               | false => error:("The register allocator replaced source constant" cy
                                             "by target constant" cy')
                               end
                 end
  end.



Definition assert_ins(args: list srcvar)(args': list impvar)(m: list (srcvar * impvar)): result unit :=
  assert (Nat.eqb (List.length args) (List.length args'))
         error:("Register allocation checker got a source variable list" args
                "whose length does not match its corresponding target variable list" args');;
  assert (List.forallb (fun p => if List.find (mapping_eqb p) m then true else false)
                       (List.combine args args'))
         error:("Register allocation checker got a source variable list" args
                "and a target variable list" args'
                "that are incompatible with its current mapping of source to target variables" m);;
  assert (List.forallb (fun '(x, x') => if check_regs x x' then true else false)
                       (List.combine args args'))
         error:("Register allocation checker got a source variable list" args
                "and a target variable list" args'
                "in which at least one source register variable is on the stack in the target.").

Definition check_bcond(m: list (srcvar * impvar))(c: bcond)(c': bcond'): result unit :=
  match c, c' with
  | CondBinary op y z, CondBinary op' y' z' =>
    assert_in y y' m;;
    assert_in z z' m;;
    assert (bbinop_beq op op')
           error:("Register allocation checker found a" op' "that should be a" op)
  | CondNez y, CondNez y' =>
    assert_in y y' m
  | _, _ => error:("Register allocation checker cannot match" c "and" c')
  end.

Definition assignment(m: list (srcvar * impvar))(x: srcvar)(x': impvar): result (list (srcvar * impvar)) :=
  if check_regs x x' then
    Success ((x, x') :: (remove_by_snd Z.eqb x' (remove_by_fst String.eqb x m)))
  else
    error:("Register allocation checker got an assignment of source register variable" x
           "to target stack variable" x'
           "but source register variables must be in registers in the target.").

Fixpoint assignments(m: list (srcvar * impvar))(xs: list srcvar)(xs': list impvar):
  result (list (srcvar * impvar)) :=
  match xs, xs' with
  | x :: xs0, x' :: xs0' =>
      a <- assignment m x x';;
      assignments a xs0 xs0'
  | nil, nil => Success m
  | _, _ => error:("Register allocator checker got variable lists of different length")
  end.

Section LoopInv.
  Context (check: list (srcvar * impvar) -> stmt -> stmt' -> result (list (srcvar * impvar)))
          (s1 s2: stmt)(s1' s2': stmt').

  (* Probably one iteration to compute the invariant, and another one to check that it
     doesn't change any more, ie 2 iterations, is enough, but that might be hard to prove.
     `List.length m` is enough fuel because the size can decrease at most that many times
     before we get to an empty invariant. *)
  Fixpoint loop_inv'(fuel: nat)(m: list (srcvar * impvar)): result (list (srcvar * impvar)) :=
    match fuel with
    | O => error:("Loop invariant calculation of register allocation checker ran out of fuel")
    | S fuel' =>
      m1 <- check m s1 s1';;
      m2 <- check m1 s2 s2';;
      let cand := list_intersect mapping_eqb m m2 in
      if Nat.eqb (List.length m) (List.length cand)
      then Success cand
      else loop_inv' fuel' cand
    end.
End LoopInv.

(* does 2 things at once: checks that the correct variables are read and computes the bindings
   that hold after executing the statement *)
(* m: conservative underapproximation of which impvar stores which srcvar *)
Fixpoint check(m: list (srcvar * impvar))(s: stmt)(s': stmt'){struct s}: result (list (srcvar * impvar)) :=
  let err := error:("Register allocation checker cannot match" s "and" s') in
  match s, s' with
  | SLoad sz x y ofs, SLoad sz' x' y' ofs' =>
    assert_in y y' m;;
    assert (Z.eqb ofs ofs') err;;
    assert (access_size_beq sz sz') err;;
    assignment m x x'
  | SStore sz x y ofs, SStore sz' x' y' ofs' =>
    assert_in x x' m;;
    assert_in y y' m;;
    assert (Z.eqb ofs ofs') err;;
    assert (access_size_beq sz sz') err;;
    Success m
  | SInlinetable sz x bs y, SInlinetable sz' x' bs' y' =>
    assert_in y y' m;;
    (* FlatToRiscv uses x' as a tmp register, and that should not overwrite y' *)
    assert (negb (Z.eqb x' y')) err;;
    assert (access_size_beq sz sz') err;;
    assert (List.list_eqb Byte.eqb bs bs') err;;
    assignment m x x'
  | SStackalloc x n body, SStackalloc x' n' body' =>
    assert (Z.eqb n n') err;;
    a <- assignment m x x';;
    check a body body'
  | SLit x z, SLit x' z' =>
    assert (Z.eqb z z') err;;
    assignment m x x'
  | SOp x op y z, SOp x' op' y' z' =>
    assert_in y y' m;;
    assert_in_op z z' m;;
    assert (bopname_beq op op') err;;
    assignment m x x'
  | SSet x y, SSet x' y' =>
    assert_in y y' m;;
    assignment m x x'
  | SIf c s1 s2, SIf c' s1' s2' =>
    check_bcond m c c';;
    m1 <- check m s1 s1';;
    m2 <- check m s2 s2';;
    Success (list_intersect mapping_eqb m1 m2)
  | SLoop s1 c s2, SLoop s1' c' s2' =>
    inv <- loop_inv' check s1 s2 s1' s2' (S (List.length m)) m;;
    m1 <- check inv s1 s1';;
    check_bcond m1 c c';;
    m2 <- check m1 s2 s2';;
    Success m1
  | SSeq s1 s2, SSeq s1' s2' =>
    m1 <- check m s1 s1';;
    check m1 s2 s2'
  | SSkip, SSkip =>
    Success m
  | SCall binds f args, SCall binds' f' args'
  | SInteract binds f args, SInteract binds' f' args' =>
    assert (String.eqb f f') err;;
    assert_ins args args' m;;
    assignments m binds binds'
  | _, _ => error:("Register allocation checker cannot match" s "and" s')
  end.

Definition check_func: list srcvar * list srcvar * stmt -> list impvar * list impvar * stmt' -> result unit :=
  fun '(args, rets, body) '(args', rets', body') =>
    assert (List.list_eqb Z.eqb (List.dedup Z.eqb args') args')
           error:("Register allocation checker got target arg variables with duplicates:" args');;
    assert (List.list_eqb Z.eqb (List.dedup Z.eqb rets') rets')
           error:("Register allocation checker got target ret variables with duplicates:" rets');;
    m0 <- assignments [] args args';;
    m1 <- check m0 body body';;
    assert_ins rets rets' m1.

Section WithEnv.
  Context {srcEnv: map.map String.string (list srcvar * list srcvar * stmt)}.
  Context {impEnv: map.map String.string (list impvar * list impvar * stmt')}.

  Definition lookup_and_check_func(e': impEnv)(fname: String.string)(impl: list srcvar * list srcvar * stmt) :=
    match map.get e' fname with
    | Some impl' => check_func impl impl'
    | None => error:("Register allocation checker could not find function" fname "in target env")
    end.

  Definition check_funcs(e: srcEnv)(e': impEnv): result unit :=
    map.forall_success (lookup_and_check_func e') e.

  Definition regalloc_functions(e: srcEnv): result impEnv :=
    e' <- map.try_map_values regalloc_function e;;
    check_funcs e e';; Success e'.
End WithEnv.

Definition loop_inv(corresp: list (srcvar * impvar))(s1 s2: stmt)(s1' s2': stmt'): list (srcvar * impvar) :=
  match loop_inv' check s1 s2 s1' s2' (S (List.length corresp)) corresp with
  | Success inv => inv
  | Failure _ => []
  end.

Definition extends(m1 m2: list (srcvar * impvar)): Prop :=
  forall x x', assert_in x x' m2 = Success tt -> assert_in x x' m1 = Success tt.

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
  unfold extends, assert_in. simpl. intros. fwd.
  destruct_one_match_hyp. 1: reflexivity.
  epose proof (H _ _ _) as A. destruct_one_match_hyp. 2: discriminate. rewrite E2. reflexivity.
  Unshelve. rewrite E. rewrite E0. reflexivity.
Qed.

Lemma extends_cons_l: forall a l,
    extends (a :: l) l.
Proof.
  unfold extends, assert_in. simpl. intros. fwd.
  destruct_one_match. 1: reflexivity.
  destruct_one_match_hyp; discriminate.
Qed.

Lemma extends_cons_r: forall a l1 l2,
    In a l1 ->
    extends l1 l2 ->
    extends l1 (a :: l2).
Proof.
  unfold extends, assert_in. simpl. intros. fwd.
  destruct_one_match_hyp. 2: {
    specialize (H0 x x'). rewrite E in H0. rewrite E0 in H0.
    eapply H0. reflexivity.
  }
  destruct_one_match. 1: reflexivity.
  eapply find_none in E2. 2: eassumption.
  simpl in E2. exfalso. congruence.
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
    loop_inv' check s1 s2 s1' s2' fuel corresp1 = Success corresp2 ->
    extends corresp1 corresp2.
Proof.
  induction fuel; simpl; intros.
  - discriminate.
  - fwd. destruct_one_match_hyp.
    + fwd. symmetry in E1. eapply intersect_same_length in E1.
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
    loop_inv' check s1 s2 s1' s2' fuel corresp = Success inv ->
    check inv s1 s1' = Success m1 ->
    check m1 s2 s2' = Success m2 ->
    inv = list_intersect mapping_eqb inv m2.
Proof.
  induction fuel; intros; simpl in *.
  - discriminate.
  - fwd. destruct_one_match_hyp.
    + fwd. symmetry in E1. eapply intersect_same_length in E1. rewrite E1 in H0.
      rewrite E in H0. fwd.
      rewrite E0 in H1. fwd.
      rewrite <- E1 at 1. reflexivity.
    + eapply IHfuel; eassumption.
Qed.

(* Similar effect as unfolding loop_inv where loop_inv's definition does not involve fuel,
   ie this lemma allows us to prove `inv = intersect inv (update inv loop_body)` *)
Lemma defuel_loop_inv: forall corresp inv m1 m2 s1 s2 s1' s2',
    inv = loop_inv corresp s1 s2 s1' s2' ->
    check inv s1 s1' = Success m1 ->
    check m1 s2 s2' = Success m2 ->
    inv = list_intersect mapping_eqb inv m2.
Proof.
  unfold loop_inv. intros. subst. destruct_one_match. 2: reflexivity.
  eapply defuel_loop_inv'; eassumption.
Qed.

Section CheckerCorrect.

  Context {width} {BW: Bitwidth width} {word: word.word width} {word_ok: word.ok word}.
  Context {mem: map.map word byte}.
  Context {srcLocals: map.map srcvar word}.
  Context {impLocals: map.map impvar word}.
  Context {srcLocalsOk: map.ok srcLocals}.
  Context {impLocalsOk: map.ok impLocals}.
  Context {srcEnv: map.map String.string (list srcvar * list srcvar * stmt)} {srcEnvOk: map.ok srcEnv}.
  Context {impEnv: map.map String.string (list impvar * list impvar * stmt')} {impEnvOk: map.ok impEnv}.
  Context {ext_spec: LeakageSemantics.ExtSpec}.
  Context {pick_sp: PickSp}.

  Definition states_compat(st: srcLocals)(corresp: list (srcvar * impvar))(st': impLocals) :=
    forall (x: srcvar) (x': impvar),
      assert_in x x' corresp = Success tt ->
      forall w,
        map.get st x = Some w ->
        map.get st' x' = Some w.

  Definition states_compat_op(st: srcLocals)(corresp: list (srcvar * impvar))(st': impLocals) :=
    forall (x: @operand srcvar) (x': @operand impvar),
      assert_in_op x x' corresp = Success tt ->
      forall w,
        exec.lookup_op_locals st x = Some w ->
        exec.lookup_op_locals st' x' = Some w.

  Lemma states_compat_then_op:
    forall st corresp st', states_compat st corresp st' -> states_compat_op st corresp st'.
  Proof.
    intros. unfold states_compat_op. destruct x, x'; unfold assert_in_op; unfold exec.lookup_op_locals; unfold states_compat in H.
    { apply H. }
    { intros. discriminate H0. }
    { intros. discriminate H0. }
    { destruct (c =? c0) eqn:Ec; try apply Z.eqb_eq in Ec; intros.
      { rewrite <- Ec. apply H1. }
      { discriminate H0. }
    }
  Qed.


  Definition precond(corresp: list (srcvar * impvar))(s: stmt)(s': stmt'): list (srcvar * impvar) :=
    match s, s' with
    | SLoop s1 c s2, SLoop s1' c' s2' => loop_inv corresp s1 s2 s1' s2'
    | _, _ => corresp
    end.

  Lemma states_compat_eval_bcond: forall lH lL c c' b corresp,
      check_bcond corresp c c' = Success tt ->
      eval_bcond lH c = Some b ->
      states_compat lH corresp lL ->
      eval_bcond lL c' = Some b.
  Proof.
    intros. rename H1 into C. unfold states_compat in C.
    destruct c; cbn in *; fwd;
      repeat match goal with
             | u: unit |- _ => destruct u
             end;
      unfold assert in *;
      cbn; fwd;
      repeat match goal with
             | H: @eq bool _ _ |- _ => autoforward with typeclass_instances in H
             end;
      subst;
      erewrite ?C by eauto; reflexivity.
  Qed.

  Lemma states_compat_eval_bcond_None: forall lH lL c c' corresp,
      check_bcond corresp c c' = Success tt ->
      eval_bcond lH c <> None ->
      states_compat lH corresp lL ->
      eval_bcond lL c' <> None.
  Proof.
    intros. destr (eval_bcond lH c). 2: congruence.
    erewrite states_compat_eval_bcond; eassumption.
  Qed.

  Lemma states_compat_eval_bcond_bw: forall lH lL c c' b corresp,
      check_bcond corresp c c' = Success tt ->
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
      assert_in y y' corresp = Success tt ->
      map.get lH y = Some v ->
      map.get lL y' = Some v.
  Proof. unfold states_compat. eauto. Qed.

  Lemma states_compat_get_op: forall corresp lL lH y y' v,
      states_compat_op lH corresp lL ->
      assert_in_op y y' corresp = Success tt ->
      exec.lookup_op_locals lH y = Some v ->
      exec.lookup_op_locals lL y' = Some v.
  Proof. unfold states_compat_op. eauto. Qed.

  Lemma states_compat_getmany: forall corresp lL lH ys ys' vs,
      states_compat lH corresp lL ->
      assert_ins ys ys' corresp = Success tt ->
      map.getmany_of_list lH ys = Some vs ->
      map.getmany_of_list lL ys' = Some vs.
  Proof.
    induction ys; intros.
    - unfold assert_ins in *. cbn in *. fwd. destruct ys'. 2: discriminate. reflexivity.
    - cbn in *. unfold assert_ins, assert in H0. fwd.
      destruct ys' as [|a' ys']. 1: discriminate.
      inversion E3. clear E3.
      cbn in *. fwd.
      erewrite states_compat_get; try eassumption. 2: {
        unfold assert_in. unfold mapping_eqb. rewrite E1. destruct H1p0 as [H1|]; [now rewrite H1|discriminate].
      }
      unfold map.getmany_of_list in *.
      erewrite IHys; eauto.
      unfold assert_ins. rewrite H1p1. rewrite H0. rewrite Nat.eqb_refl. simpl.
      unfold assert. rewrite E4p1. reflexivity.
  Qed.

  Lemma states_compat_put: forall lH corresp lL x x' v m,
      assignment corresp x x' = Success m ->
      states_compat lH corresp lL ->
      states_compat (map.put lH x v) m (map.put lL x' v).
  Proof.
    intros. unfold states_compat in *. intros k k'. intros.
    rewrite map.get_put_dec. rewrite map.get_put_dec in H2.
    unfold assert_in, assignment in H, H0, H1. fwd. simpl in E.
    rewrite String.eqb_sym, Z.eqb_sym in E.
    destr (Z.eqb x' k').
    - destr (String.eqb x k).
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
      + eapply H0. 2: eassumption. unfold assert_in.
        destruct_one_match. 1: rewrite E0; trivial.
        eapply find_none in E3. 2: eassumption.
        simpl in E3. rewrite String.eqb_refl, Z.eqb_refl in E3. discriminate.
  Qed.



  Lemma putmany_of_list_zip_states_compat: forall binds binds' resvals lL lH l' corresp corresp',
      map.putmany_of_list_zip binds resvals lH = Some l' ->
      assignments corresp binds binds' = Success corresp' ->
      states_compat lH corresp lL ->
      exists lL',
        map.putmany_of_list_zip binds' resvals lL = Some lL' /\
        states_compat l' corresp' lL'.
  Proof.
    induction binds; intros.
    - simpl in H. fwd. destruct binds'. 2: discriminate.
      simpl in *. fwd. eauto.
    - simpl in *. fwd.
      specialize IHbinds with (1 := H).
      rename l' into lH'.
      edestruct IHbinds as (lL' & P & C). 1: eassumption. 1: eapply states_compat_put. 1: eassumption. 1: eassumption.
      simpl. rewrite P. eauto.
  Qed.

  Lemma assignments_same_length: forall xs xs' m1 m2,
      assignments m1 xs xs' = Success m2 -> List.length xs = List.length xs'.
  Proof.
    induction xs; intros; destruct xs'; try discriminate.
    - reflexivity.
    - simpl in *. f_equal. destruct_one_match_hyp; try discriminate.
      specialize (IHxs xs' a0 m2). eauto.
  Qed.

  Lemma assert_ins_same_length: forall xs xs' m u,
      assert_ins xs xs' m = Success u -> List.length xs = List.length xs'.
  Proof.
    unfold assert_ins, assert. intros. fwd. assumption.
  Qed.

  Opaque isRegStr.
  Opaque isRegZ.

  Lemma assert_in_then_check_regs_op : forall x x' corresp,
    assert_in_op x x' corresp = Success tt -> check_regs_op x x' = true.
  Proof.
    unfold check_regs_op, assert_in_op, assert_in; intros; destruct x'; fwd; reflexivity.
  Qed.

  Ltac discr_match_success :=
    match goal with
    | H: match ?expr with _ => _ end = Success _ |- _ => destr expr; discriminate
    end.

  Lemma check_regs_cost_SIf:
    forall (cond : bcond) (bThen bElse : stmt) (corresp : list (string * Z))
      (cond0 : bcond') (s'1 s'2 : stmt') (a0 a1 : list (string * Z))
      (mc mcL : MetricLog),
      check_bcond corresp cond cond0 = Success tt ->
      check corresp bThen s'1 = Success a0 ->
      check corresp bElse s'2 = Success a1 ->
      forall mc' mcH' : MetricLog,
        (mc' - exec.cost_SIf isRegZ cond0 mcL <= mcH' - exec.cost_SIf isRegStr cond mc)%metricsH ->
        (mc' - mcL <= mcH' - mc)%metricsH.
  Proof.
    intros.
    repeat (unfold check_bcond, assert_in, assignment in *; fwd).
    destr cond; destr cond0;
    repeat match goal with
           | H: match ?expr with _ => _ end = Success _ |- _ => destr expr; try discriminate
           end;
    unfold check_regs, exec.cost_SIf in *;
    cost_solve.
  Qed.

  Lemma check_regs_cost_SLoop_false:
  forall (cond : bcond) (body1 body2 : stmt) (corresp' : list (string * Z)) (s'1 : stmt')
      (cond0 : bcond') (s'2 : stmt') (mc mcL : MetricLog) (a : list (string * Z)),
    check a body1 s'1 = Success corresp' ->
    check_bcond corresp' cond cond0 = Success tt ->
    forall a2 : list (string * Z),
    check corresp' body2 s'2 = Success a2 ->
    forall mc' mcH' : MetricLog,
    (mc' - mcL <= mcH' - mc)%metricsH ->
    (exec.cost_SLoop_false isRegZ cond0 mc' - mcL <= exec.cost_SLoop_false isRegStr cond mcH' - mc)%metricsH.
  Proof.
    intros.
    repeat (unfold check_bcond, assert_in, assignment in *; fwd).
    destr cond; destr cond0;
    repeat match goal with
           | H: match ?expr with _ => _ end = Success _ |- _ => destr expr; try discriminate
           end;
    unfold check_regs, exec.cost_SLoop_false in *;
    cost_solve.
  Qed.

  Hint Constructors exec.exec : checker_hints.
  Hint Resolve states_compat_get : checker_hints.
  Hint Resolve states_compat_put : checker_hints.
  Hint Resolve states_compat_get_op : checker_hints.
  Hint Resolve states_compat_then_op : checker_hints.
  (*Hint Resolve*)
  (*     check_regs_cost_SLoad check_regs_cost_SStore check_regs_cost_SInlinetable*)
  (*     check_regs_cost_SStackalloc check_regs_cost_SLit (*check_regs_cost_SOp*)*)
  (*     check_regs_cost_SSet check_regs_cost_SIf check_regs_cost_SLoop_false*)
  (*  : checker_hints.*)

  Ltac a :=
    repeat match goal with | |- metricsLeq _ _ => fail 1 | _ => econstructor end;
    eauto 10 with checker_hints.

  Ltac b := unfold assert_in, assignment, check_regs in *; cost_hammer.

  Lemma checker_correct: forall (e: srcEnv) (e': impEnv) s q aep k t m lH mcH post,
      check_funcs e e' = Success tt ->
      exec PreSpill isRegStr e s q aep k t m lH mcH post ->
      forall lL corresp corresp' s' mcL,
      check corresp s s' = Success corresp' ->
      states_compat lH (precond corresp s s') lL ->
      exec PreSpill isRegZ e' s' q aep k t m lL mcL (fun q' aep' k' t' m' lL' mcL' =>
        exists lH' mcH', (q' = true -> states_compat lH' corresp' lL') /\
                    (mcL' - mcL <= mcH' - mcH)%metricsH /\
                    post q' aep' k' t' m' lH' mcH').
  Proof.
    induction 2; intros;
      match goal with
      | H: check _ _ _ = Success _ |- _ => pose proof H as C; move C at top; cbn [check] in H
      end;
      fwd;
      repeat match goal with
             | u: unit |- _ => destruct u
             end;
      unfold assert in *;
      fwd;
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
      repeat eexists; eauto; cost_solve.
    - (* Case exec.call *)
      rename binds0 into binds', args0 into args'.
      unfold check_funcs in H.
      eapply map.get_forall_success in H. 2: eassumption.
      unfold lookup_and_check_func in *. fwd.
      destruct p as ((params' & rets') & fbody').
      unfold check_func in *. fwd.
      apply_in_hyps @map.getmany_of_list_length.
      apply_in_hyps assert_ins_same_length.
      apply_in_hyps assignments_same_length.
      apply_in_hyps @map.putmany_of_list_zip_sameLength.
      assert (length params' = length argvs) as L3 by congruence.
      eapply map.sameLength_putmany_of_list in L3. destruct L3 as [lLF' L3].
      eapply @exec.call. 1: eassumption. 1: eauto using states_compat_getmany. 1: exact L3.
      + eapply IHexec. 1: eassumption. eapply states_compat_precond.
        edestruct putmany_of_list_zip_states_compat as [ lLF0 [L SC] ].
        2: exact E3. 2: eapply states_compat_empty. 1: eassumption.
        rewrite L3 in L. apply Option.eq_of_eq_Some in L. subst lLF0. exact SC.
      + cbv beta. intros. fwd. specialize H4 with (1 := H7p2). destruct q'.
        * specialize (H7p0 eq_refl). destruct H4 as (retvs & lHF' & G & P & Hpost).
          edestruct putmany_of_list_zip_states_compat as (lL' & L4 & SC).
          1: exact P. 1: exact H5. 1: eassumption.
          do 2 eexists. ssplit.
          -- eapply states_compat_getmany; eassumption.
          -- exact L4.
          -- repeat eexists. 6: eassumption. 1: intros; exact SC.
             all: cost_solve.
        * eexists. eexists. intuition eauto. 1: congruence. b.
    - (* Case exec.load *)
      a. b.
    - (* Case exec.store *)
      a. b.
    - (* Case exec.inlinetable *)
      a. b.
    - (* Case exec.stackalloc *)
      eapply exec.stackalloc. 1: assumption.
      intros. eapply exec.weaken.
      + eapply H2; try eassumption.
        eapply states_compat_precond. eapply states_compat_put; eassumption.
      + cbv beta. intros. fwd. destruct q'.
        -- fwd. eexists. eexists. do 2 (split; try eassumption).
           eexists. eexists. do 2 (split; try eassumption).
           b.
        -- eexists. eexists. ssplit; [congruence| |eassumption]. b.
    - (* Case exec.lit *)
      a. b.
    - (* Case exec.op *)
      a.
      unfold assert_in_op, assert_in, assignment, check_regs in *; scost_hammer. (* could be faster *)
    - (* Case exec.set *)
      a. b.
    - (* Case exec.if_true *)
      eapply exec.if_true. 1: eauto using states_compat_eval_bcond.
      eapply exec.weaken.
      + eapply IHexec. 1: eassumption.
        eapply states_compat_precond. eassumption.
      + cbv beta. intros. fwd. eexists. eexists. split. 2: split. 3: eassumption.
        1: intros; eapply states_compat_extends; eauto. 1: eapply extends_intersect_l.
        eapply check_regs_cost_SIf; eauto.
    - (* Case exec.if_false *)
      eapply exec.if_false. 1: eauto using states_compat_eval_bcond.
      eapply exec.weaken.
      + eapply IHexec. 1: eassumption.
        eapply states_compat_precond. eassumption.
      + cbv beta. intros. fwd. eexists. eexists. split. 2: split. 3: eassumption.
        1: intros; eapply states_compat_extends; eauto. 1: eapply extends_intersect_r.
        eapply check_regs_cost_SIf; eauto.
    - (* Case exec.loop *)
      rename H4 into IH2, IHexec into IH1, H6 into IH12.
      match goal with
      | H: states_compat _ _ _ |- _ => rename H into SC
      end.
      pose proof SC as SC0.
      unfold loop_inv in SC.
      rewrite E in SC.
      eapply exec.loop_cps. eapply exec.weaken.
      1: eapply IH1; eauto using states_compat_precond.
      cbv beta. intros. fwd. destruct q'.
      + destruct (eval_bcond l' cond0) eqn:Ee.
        2: { exfalso. eapply states_compat_eval_bcond_None; eauto. }
        exists b. intuition; subst.
        -- cbv beta. intros. fwd. eexists. eexists. (* exists (exec.cost_SLoop_false isRegStr cond mcH'). *)
           split. 2: split. 3: eauto using states_compat_eval_bcond_bw.
           1: intros; assumption.
           eapply check_regs_cost_SLoop_false. 1: apply E0. all: eauto.
        -- cbv beta. intros. fwd. eapply exec.weaken. 1: eapply IH2; eauto using states_compat_eval_bcond_bw.
           1: eapply states_compat_precond; eauto.
           cbv beta. intros. fwd. Search mid2. specialize H7 with (1 := H6p2).
           move H7 at bottom. specialize H7 with (1 := C). simpl in H7.
           destruct q'.
           ++ eapply exec.weaken.
              --- eapply H7. 
                  eapply states_compat_extends. 2: eauto.
                  pose proof defuel_loop_inv as P.
                  specialize P with (2 := E0).
                  specialize P with (2 := E2).
                  specialize (P corresp).
                  unfold loop_inv in P|-*.
                  rewrite E in P. rewrite E.
                  specialize (P eq_refl).
                  rewrite P.
                  eapply extends_intersect_r.
              --- cbv beta. intros. fwd. eexists. eexists. split. 2: split. 1: eauto. 2: eauto.
                  specialize (H6p0 eq_refl).
                  cbv [states_compat] in H6p0.
                  repeat (unfold check_bcond, assert_in, assignment in *; fwd).
                  Print states_compat.
          (*clear -E0 E1 E2 H4p1p0 H4p1p1 H4p1 H4p3. TODO fix this*)
          intros; unfold check_regs in *; cbn in *; unfold exec.cost_SLoop_true in *; try discr_match_success;
            destr cond; destr cond0; destr (isRegStr x); destr (isRegZ x0); try (destr (isRegStr y)); try (destr (isRegZ y0));
            try discriminate; try discr_match_success.
          all: cost_solve.
           ++ Search mid2. specialize IH12 with (1 := H6p2). move IH12 at bottom.
              inversion IH12. subst. apply exec.quit. eexists. eexists. intuition eauto.
              1: congruence.
              (*TODO make this faster?*)
              unfold states_compat in H4.
              repeat (unfold check_bcond, assert_in, assignment in *; fwd).
              intros; unfold check_regs in *; cbn in *; unfold exec.cost_SLoop_true in *; try discr_match_success;
                destr cond; destr cond0; destr (isRegStr x); destr (isRegZ x0); try (destr (isRegStr y)); try (destr (isRegZ y0));
                try discriminate; try discr_match_success.
              all: cost_solve.
      + eauto 10.
        
    - (* Case exec.seq *)
      rename H2 into IH2, IHexec into IH1.
      eapply exec.seq.
      + eapply IH1. 1: eassumption.
        eapply states_compat_precond. assumption.
      + cbv beta. intros ? ? k' t' m' l' mcblah ?. fwd. destruct q'.
        -- eapply IH2 in H2p2. 2,3: eauto using states_compat_precond.
           eapply exec.weaken; eauto.
           cbv beta. intros. fwd. exists lH'0. exists mcH'0. split. 2:split. 1,3: eauto.
           b.
        -- Search mid. apply H1 in H2p2. inversion H2p2. subst. apply exec.quit.
           eexists. eexists. intuition eauto. congruence.
    - (* case exec.skip *)
      a. b.
    - apply exec.quit. do 2 eexists. intuition eauto. 1: congruence. cost_hammer.
    - apply exec.exec_A. eauto.
    - eapply exec.exec_E. eauto.
  Qed.

End CheckerCorrect.
