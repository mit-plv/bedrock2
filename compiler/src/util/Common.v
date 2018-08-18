Require Export Coq.omega.Omega.
Require Export Coq.Lists.List.
Require Export riscv.util.Word.
Require Export riscv.util.Monads.
Require Export compiler.Decidable.
Require Export compiler.util.Tactics.
Require Export compiler.util.Set.
Require Export compiler.util.Map.
Require Export lib.fiat_crypto_tactics.UniquePose.

Global Instance dec_eq_word : forall sz, DecidableEq (word sz) := @weq_dec.

Lemma nth_error_nth: forall {T: Type} (l: list T) (e d: T) (i: nat),
  nth_error l i = Some e ->
  nth i l d = e.
Proof.
  intros T l. induction l; intros.
  - destruct i; simpl in H; discriminate.
  - destruct i; simpl in H; inversion H; subst.
    + reflexivity.
    + simpl. auto.
Qed.

Fixpoint option_all {A} (l : list (option A)) {struct l} : option (list A) :=
  match l with
  | nil => Some nil
  | (Some x)::l =>
    match option_all l with
    | Some l' => Some (x::l')
    | _ => None end
  | _ => None
  end.

Section WithMap.
  Context {K V} {TMap: MapFunctions K V}.
  Fixpoint putmany (keys : list K) (values : list V) (init : map K V) {struct keys} : option (map K V) :=
    match keys, values with
    | nil, nil => Return init
    | b::binders, v::values => t <- putmany binders values init; Return (put t b v)
    | _, _ => None
    end.

  Lemma putmany_sameLength : forall bs vs st st' (H:putmany bs vs st = Some st'),
      length bs = length vs.
  Proof.
    induction bs, vs; cbn; try discriminate; trivial; [].
    intros; destruct (putmany bs vs st) eqn:?; [eauto using f_equal|discriminate].
  Qed.
End WithMap.
