Require Import bedrock2.Macros bedrock2.Syntax.
Require Import bedrock2.BasicC64Syntax bedrock2.BasicALU bedrock2.NotationsInConstr.

Import BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Existing Instance bedrock2.BasicC64Syntax.Basic_bopnames_params.
Local Coercion literal (z : Z) : expr := expr.literal z.
Local Coercion var (x : string) : expr := expr.var x.

Definition ipow := ("ipow", (["x";"e"], (["ret"]:list varname), bedrock_func_body:(
  "ret" = 1;;
  while ("e") {{
    if ("e" .& 1) {{ "ret" = "ret" * "x" }};;
    "e" = "e" >> 1;;
    "x" = "x" * "x"
  }}
))).

Require Import bedrock2.Semantics bedrock2.BasicC64Semantics bedrock2.Map.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
Require bedrock2.WeakestPrecondition bedrock2.WeakestPreconditionProperties.
Require bedrock2.TailRecursion.

Section WithT.
  Context {T : Type}.
  Fixpoint bindcmd (c : cmd) (k : cmd -> T) {struct c} : T :=
    match c with
    | cmd.cond e c1 c2 => bindcmd c1 (fun c1 => bindcmd c2 (fun c2 => let c := cmd.cond e c1 c2 in k c))
    | cmd.seq c1 c2 => bindcmd c1 (fun c1 => bindcmd c2 (fun c2 => let c := cmd.seq c1 c2 in k c))
    | cmd.while e c => bindcmd c (fun c => let c := cmd.while e c in k c)
    | c => let c := c in k c
    end.
End WithT.

Definition spec_of_ipow := fun functions =>
  forall x e t m,
    WeakestPrecondition.call (fun _ => True) (fun _ => False) (fun _ _ => False) functions
      (fst ipow) t m [x; e]
      (fun t' m' rets => t=t'/\ m=m' /\ exists v, rets = [v]).

Ltac bind_body_of_function f :=
  let fname := open_constr:(_) in
  let fargs := open_constr:(_) in
  let frets := open_constr:(_) in
  let fbody := open_constr:(_) in
  let funif := open_constr:((fname, (fargs, frets, fbody))) in
  unify f funif;
  let G := lazymatch goal with |- ?G => G end in
  let P := lazymatch eval pattern ipow in G with ?P _ => P end in
  change (bindcmd fbody (fun c : cmd => P (fname, (fargs, frets, c))));
  cbv beta iota delta [bindcmd]; intros.

Tactic Notation "eabstract" tactic3(tac) :=
  let G := match goal with |- ?G => G end in
  let pf := lazymatch constr:(ltac:(tac) : G) with ?pf => pf end in
  abstract exact_no_check pf.

Ltac refine_ex :=
  hnf;
  let P := lazymatch goal with |- ex ?P => P end in
  refine (let l := _ in ex_intro P l _).

Ltac refine_ex_and :=
  hnf;
  let P := lazymatch goal with |- ex ?P => P end in
  refine (let l := _ in ex_intro P l (conj _ _)).

Ltac break_ex :=
  repeat match goal with
         | H: exists _, _ |- _ => destruct H
         end.
Ltac break_and :=
  repeat match goal with
         | H: _ /\ _ |- _ => destruct H
         end.

Ltac subst_and_bind_all :=
  repeat match goal with
  | H: ?x = ?v |- _ =>
    assert_succeeds (subst x);
    let x' := fresh "x" in rename x into x';
    simple refine (let x := v in _);
    change (x' = x) in H;
    symmetry in H;
    destruct H
  end.

(* FIXME: this is a hack as it may reduce in the values as well *)
Ltac reduce_locals_map :=
cbv [
    locals parameters
    map.put map.get map.empty
    SortedListString.map
    SortedList.parameters.key SortedList.parameters.value
    SortedList.parameters.key_eqb SortedList.parameters.key_ltb
    SortedList.map SortedList.sorted SortedList.put
    SortedList.value SortedList.ok SortedList.minimize_eq_proof
    String.eqb String.ltb String.prefix
    Ascii.eqb Ascii.ltb Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect
    Ascii.N_of_ascii Ascii.N_of_digits
    BinNatDef.N.ltb BinNatDef.N.eqb BinNatDef.N.compare BinNat.N.add BinNat.N.mul
    Pos.mul Pos.add Pos.eqb Pos.ltb Pos.compare Pos.compare_cont
    Bool.bool_dec bool_rec bool_rect sumbool_rec sumbool_rect
    andb orb
  ].

Lemma shiftr_decreases
      (x1 : Word.word 64)
      (n : Word.wzero 64 <> x1)
  : (Word.wordToNat (Word.wrshift' x1 1) < Word.wordToNat x1)%nat.
  SearchAbout Word.wrshift'.
  cbv [Word.wrshift'].
Admitted.

Set Printing Depth 999999.
Local Notation "'need!' y 's.t.' Px 'let' x ':=' v 'using' pfPx 'in' pfP" :=
  (let x := v in ex_intro (fun y => Px /\ _) x (conj pfPx pfP))
  (right associativity, at level 200, pfPx at next level,
    format "'need!'  y  's.t.'  Px  '/' 'let'  x  ':='  v  'using'  pfPx  'in'  '/' pfP").
Local Notation "'need!' x 's.t.' Px 'let' x ':=' v 'using' pfPx 'in' pfP" :=
  (let x := v in ex_intro (fun x => Px /\ _) x (conj pfPx pfP))
  (only printing, right associativity, at level 200, pfPx at next level,
    format "'need!'  x  's.t.'  Px  '/' 'let'  x  ':='  v  'using'  pfPx  'in'  '/' pfP").
Local Notation "'need!' y 's.t.' Px 'let' x ':=' v 'using' pfPx 'in' pfP" :=
  (let x := v in ex_intro (fun y => Px /\ _) x (conj pfPx pfP))
  (right associativity, at level 200, pfPx at next level,
   format "'need!'  y  's.t.'  Px  '/' 'let'  x  ':='  v  'using'  pfPx  'in'  '/' pfP")
  : type_scope.
Local Notation "'need!' x 's.t.' Px 'let' x ':=' v 'using' pfPx 'in' pfP" :=
  (let x := v in ex_intro (fun x => Px /\ _) x (conj pfPx pfP))
  (only printing, right associativity, at level 200, pfPx at next level,
   format "'need!'  x  's.t.'  Px  '/' 'let'  x  ':='  v  'using'  pfPx  'in'  '/' pfP")
  : type_scope.

Lemma ipow_ok : forall functions, spec_of_ipow (ipow::functions).
Proof.
  bind_body_of_function ipow.
  cbv [spec_of_ipow]. intros x0 e0 t0 m0.

  refine_ex_and.
  { exact eq_refl. }
  refine_ex_and.
  { refine_ex_and.
    { repeat (refine_ex_and || exact eq_refl). }
    exact eq_refl. }

  let T := match type of l0 with ?T => T end in
  set (P_ := fun v t m (l:T) =>
            exists x e ret,
              t = t0 /\ l = (map.put (map.put (map.put map.empty "x" x) "e" e) "ret" ret) /\ m = m0 /\ v = Word.wordToNat e);
  set (Q_ := fun (v:nat) t m (l:T) =>
            exists x e ret,
              t = t0 /\ l = (map.put (map.put (map.put map.empty "x" x) "e" e) "ret" ret) /\ m = m0);
  eapply TailRecursion.tailrec with (lt:=lt) (P:=P_) (Q:=Q_).
  exact Wf_nat.lt_wf.
  { eabstract (repeat refine_ex; repeat split; repeat exact eq_refl). }
  { intros; cbv [P_ Q_] in * |- ; break_ex; break_and; subst_and_bind_all.

    refine_ex_and.
    eabstract (repeat (refine_ex_and || exact eq_refl)).
    split; intros.
    { refine_ex_and.
      eabstract (repeat (refine_ex_and || exact eq_refl)).
      split; intros.

      { refine_ex_and.
        eabstract (repeat (refine_ex_and || exact eq_refl)).
        refine_ex_and.
        { refine_ex_and. exact eq_refl.
          refine_ex_and. exact eq_refl.
          (* [exact eq_refl] reduces too much here *)
          exact (eq_refl (interp_binop bop_sru l7 l)). }
        refine_ex_and.
        eabstract (repeat (refine_ex_and || exact eq_refl)).
        refine_ex_and.
        { repeat refine_ex. split.
          { exact eq_refl. }
          { split.
            { subst l1. eapply SortedList.eq_value; reduce_locals_map; exact eq_refl. }
            split.
            { exact eq_refl. }
            { exact eq_refl. } } }
        { split.
          { right.
            (* measure decreases *)
            abstract (
            cbv [l l6 v l3] in *;
            revert H; clear; intros H;
            cbv [parameters word_test] in H;
            destruct (Word.weq (Word.wzero 64) x1) in H; try congruence; clear H;
            cbv [parameters
                   interp_binop
                   Basic_bopnames.BasicALU
                   BasicC64Semantics.shiftWidth
                   bop_sru];
            rewrite (eq_refl 
                     : Word.wordToNat (Word.wand (Word.ZToWord 64 1) (Word.NToWord 64 (Npos 63))) = 1%nat); shelve_unifiable;
            eapply shiftr_decreases; eauto). }
        { intros; cbv [P_ Q_] in * |-; break_ex; break_and; subst_and_bind_all.
          refine_ex. refine_ex. refine_ex. split.
          { exact eq_refl. }
          split.
          { exact eq_refl. }
          { exact eq_refl. } } } }

      { refine_ex_and.
        { refine_ex_and. exact eq_refl.
          refine_ex_and. exact eq_refl.
          (* [exact eq_refl] reduces too much here *)
          exact (eq_refl (interp_binop bop_sru _ _)). }
        refine_ex_and.
        eabstract (repeat (refine_ex_and || exact eq_refl)).
        refine_ex_and.
        { repeat refine_ex. split.
          { exact eq_refl. }
          { split.
            { subst l1. eapply SortedList.eq_value; reduce_locals_map; exact eq_refl. }
            split.
            { exact eq_refl. }
            { exact eq_refl. } } }
        { split.
          { right.
            (* measure decreases *)
            abstract (
            cbv [l v l3 l5] in *;
            revert H; clear; intros H;
            cbv [parameters word_test] in H;
            destruct (Word.weq (Word.wzero 64) x1) in H; try congruence; clear H;
            cbv [parameters
                   interp_binop
                   Basic_bopnames.BasicALU
                   BasicC64Semantics.shiftWidth
                   bop_sru];
            rewrite (eq_refl 
                     : Word.wordToNat (Word.wand (Word.ZToWord 64 1) (Word.NToWord 64 (Npos 63))) = 1%nat); shelve_unifiable;
            eapply shiftr_decreases; eauto). }
        { intros; cbv [P_ Q_] in * |-; break_ex; break_and; subst_and_bind_all.
          repeat refine_ex. split.
          { exact eq_refl. }
          split.
          { exact eq_refl. }
          { exact eq_refl. } } } } }

    repeat refine_ex. split.
    { exact eq_refl. }
    split.
    { exact eq_refl. }
    { exact eq_refl. } }

  { intros; cbv [P_ Q_] in * |-; break_ex; break_and; subst_and_bind_all.
    refine_ex_and.
    { exact eq_refl. }
    { split.
      { exact eq_refl. }
      split.
      { exact eq_refl. }
      { refine_ex.
        exact eq_refl. } } }

  Unshelve.
  eapply WeakestPreconditionProperties.Proper_call; cbv; intuition idtac.
Defined.