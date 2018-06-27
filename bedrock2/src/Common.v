Require Export Coq.omega.Omega.
Require Export Coq.Lists.List.
Require Export bbv.Word.
Require Export riscv.util.Monads.
Require Export compiler.Decidable.
Require Export compiler.util.Tactics.
Require Export compiler.Set.
Require Export lib.fiat_crypto_tactics.UniquePose.

Class Map(T K V: Type) := mkMap {
  empty: T;
  get: T -> K -> option V;
  put: T -> K -> V -> T;

  get_put_same: forall (m: T) (k: K) (v: V), get (put m k v) k = Some v;
  get_put_diff: forall (m: T) (k1 k2: K) (v: V), k1 <> k2 -> get (put m k1 v) k2 = get m k2;
  empty_is_empty: forall (k: K), get empty k = None
  (* TODO probably needs some more properties *)
}.

Instance Function_Map(K V: Type){decK: DecidableEq K}: Map (K -> option V) K V := {|
  empty := fun _ => None;
  get := id;
  put := fun (m: K -> option V) (k: K) (v: V) =>
           fun (k': K) => if dec (k = k') then Some v else m k'
|}.
- intros. cbv. destruct_one_match; reflexivity || contradiction.
- intros. cbv. destruct_one_match; reflexivity || contradiction.
- intros. reflexivity.
Defined.

Global Instance dec_eq_word : forall sz, DecidableEq (word sz) := weq.

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
  Context {T} {K V} {TMap:Map T K V}.
  Fixpoint putmany (keys : list K) (values : list V) (init : T) {struct keys} : option T :=
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