
Section PowerFunc.

  Context {T: Type}.

  Definition power_func(f: T -> T): nat -> (T -> T) :=
    fix rec(n: nat) := match n with
    | O => fun x => x
    | S m => fun x => f ((rec m) x)
    end.

  Lemma power_func_one_plus_n: forall f n initial,
    power_func f n (f initial) = f (power_func f n initial).
  Proof.
    intros f n. induction n; intros.
    - reflexivity.
    - simpl. f_equal. apply IHn.
  Qed.

  (* TODO probably we won't need multiApply any more *)

  Definition multiApply(f: T -> T)(init: T): nat -> T :=
    fix rec(n: nat) := match n with
    | O => init
    | S m => f (rec m)
    end.

  Lemma multiApply_is_power_func: forall n f init,
    multiApply f init n = power_func f n init.
  Proof.
    induction n; intros.
    - reflexivity.
    - simpl. f_equal. apply IHn.
  Qed.

  Lemma multiApply_inv: forall (f: T -> T) (init: T) (n: nat),
    multiApply f init (S n) = multiApply f (f init) n.
  Proof.
    intros. simpl. induction n.
    - reflexivity.
    - simpl. f_equal. assumption.
  Qed.

End PowerFunc.
