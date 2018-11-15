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
    WeakestPrecondition.call (fun _ => True) (fun _ => False) (fun _ _ => True) functions
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
    replace x' with x by congruence; clear H
  end.

Lemma ipow_ok : forall functions, spec_of_ipow (ipow::functions).
Proof.
  bind_body_of_function ipow.
  cbv [spec_of_ipow]. intros.

  refine_ex_and.
  { exact eq_refl. }
  refine_ex_and.
  { refine_ex_and.
    { repeat (refine_ex_and || exact eq_refl). }
    exact eq_refl. }

  eapply TailRecursion.tailrecursion with
      (lt:=Z.lt)
      (P:=fun _ t' l => emp (exists x e ret, t' = t /\ l = (map.put (map.put (map.put map.empty "x" x) "e" e) "ret" ret)))
      (Q:=fun _ t' l => emp (exists x e ret, t' = t /\ l = (map.put (map.put (map.put map.empty "x" x) "e" e) "ret" ret)))
      (R0 := fun m' => m'=m).
  admit.
  admit.
  admit.
  intros.

  eapply sep_emp_l in H. destruct H.
  break_ex.
  break_and.
  subst_and_bind_all.

  refine_ex_and.
  { repeat (refine_ex_and || exact eq_refl). }
  split; intros.
  { refine_ex_and.
    { repeat (refine_ex_and || exact eq_refl). }
    split; intros.
    { refine_ex_and.
      { repeat (refine_ex_and || exact eq_refl). }
      refine_ex_and.
      { repeat (refine_ex_and || exact eq_refl). }
      refine_ex_and.
      { repeat (refine_ex_and || exact eq_refl). }
      eexists. eexists. split.
      { eapply sep_emp_l. split.
        { do 3 eexists. split; exact eq_refl. }
        { eapply sep_emp_r. split. assumption. exact I. } }
      { split.
        { admit. }
        { intros.
          eapply impl1_l_sep_emp; intros.
          admit. } } }
    { refine_ex_and.
      { repeat (refine_ex_and || exact eq_refl). }
      refine_ex_and.
      { repeat (refine_ex_and || exact eq_refl). }
      eexists. eexists. split.
      { eapply sep_emp_l. split.
        { do 3 eexists. split; exact eq_refl. }
        { eapply sep_emp_r. split. assumption. exact I. } }
      { split.
        { admit. }
        { intros.
          eapply impl1_l_sep_emp; intros.
          admit. } } } }
  { eapply sep_emp_l. split. solve[repeat eexists]. assumption. }
  intros.
  eapply sep_emp_l in H. destruct H.
  break_ex.
  break_and.
  subst_and_bind_all.
  refine_ex_and.
  { repeat (refine_ex_and || exact eq_refl). }
  repeat eexists.
Abort.