Require Import Rupicola.Lib.Api.

Section Tree.
  Context {p : Semantics.parameters}.
  Notation address := Semantics.word.

  Inductive Annotated {t : Type} :=
  | Borrowed : address -> t -> Annotated
  | Owned : t -> Annotated
  .
  Arguments Annotated : clear implicits.

  Inductive tree {alpha : Type}:=
  | Empty : tree
  | Node : alpha -> tree -> tree -> tree
  .
  Arguments tree : clear implicits.

  Section defs.
    Context {alpha : Type}.

    Fixpoint lift (t : tree alpha)
    : tree (Annotated alpha) :=
      match t with 
      | Empty => Empty
      | Node a l r =>
        Node (Owned a) (lift l) (lift r)
      end.

    Fixpoint setRoot (t : tree alpha) (a : alpha)
      : tree alpha :=
      match t with
      | Empty => Empty
      | Node _ l r => Node a l r
      end.

    Fixpoint lookup
             (t : tree alpha)
             (cond : alpha -> bool)
      : option alpha :=
      match t with
      | Empty => None
      | Node a l r =>
        if cond a then Some a
        else match lookup l cond with
             | Some a => Some a
             | None => lookup r cond
             end
      end.

    Fixpoint replace
             (t : tree alpha)
             (cond : alpha -> bool)
             (a' : alpha)
      : tree alpha * bool :=
      match t with
      | Empty => (t, false)
      | Node a l r =>
        if cond a then (Node a' l r, true)
        else match replace l cond a' with
             | (l', true) => (Node a l' r, true)
             | (_, false) =>
               match replace r cond a' with
               | (r', true) => (Node a l r', true)
               | (_,false) => (Node a l r, false)
               end
             end
      end.

    Section sep.
      Context {Alpha : Semantics.word -> alpha -> Semantics.mem -> Prop}
              {word_size_in_bytes : Z}.

      Local Notation word_offset :=
        (word.of_Z word_size_in_bytes).

      Definition AnnotatedAlpha
                 (addr : Semantics.word)
                 (x : Annotated alpha)
        : Semantics.mem -> Prop :=
        match x with
        | Borrowed p _ => emp (addr = p)
        | Owned a => Alpha addr a
        end.

      Fixpoint Tree
               (addr : Semantics.word)
               (t : tree (Annotated alpha))
        : Semantics.mem -> Prop :=
        match t with
        | Empty => emp (addr = word.of_Z 0)
        | Node a r l =>
          let laddr := word.add addr word_offset in 
          let raddr := word.add laddr word_offset in 
          sep (AnnotatedAlpha addr a)
              (sep (Tree laddr l) (Tree raddr r))
        end.
    End sep.
  End defs.

  Section proofs.
    Context {alpha : Type}.
    Lemma lift_setRoot_comm t (a : alpha) :
      setRoot (lift t) (Owned a) = lift (setRoot t a).
    Proof. destruct t; reflexivity. Qed.

    Definition liftf {T} (f : alpha -> T)
               (x : Annotated alpha) :=
      match x with
      | Borrowed _ x => f x
      | Owned x => f x
      end.

    Lemma lift_replace_comm t cond (a : alpha) :
      replace (lift t) (liftf cond) (Owned a)
      = (lift (fst (replace t cond a)),
         snd (replace t cond a)).
    Proof.
      induction t; cbn [replace lift];
        try reflexivity.
      repeat match goal with
             | _ => progress subst
             | _ => progress cbn [lift liftf fst snd] in *
             | H : (_,_) = (_,_) |- _ =>
               inversion H; clear H
             | |- context [match ?x with _ => _ end] =>
               destruct x eqn:?
             | _ => reflexivity
             end.
    Qed.

    Section sep.
      Context
        {ok : Semantics.parameters_ok p}
        {Alpha : Semantics.word -> alpha -> Semantics.mem -> Prop}
        {word_size_in_bytes : Z}.

      Local Notation word_offset :=
        (word.of_Z word_size_in_bytes).
      Local Notation Tree :=
        (@Tree _ Alpha word_size_in_bytes).

      Lemma lookup_replace t cond :
        forall a olda pt pa R mem,
          sep (sep (Tree pt t) (Alpha pa a)) R mem ->
          lookup t cond = Some (Borrowed pa olda) ->
          sep (Tree pt (fst (replace t cond (Owned a)))) R mem.
      Proof.
        induction t; intros;
          repeat match goal with
                 | _ => progress subst
                 | _ => progress cbn in *
                 | H : Some _ = Some _ |- _ =>
                   inversion H; clear H
                 | H : context [match ?x with _ => _ end] |- _ =>
                   destruct x eqn:?
                 | |- context [match ?x with _ => _ end] =>
                   destruct x eqn:?
                 | H : sep (sep (sep _ _) _) _ _ |- _ =>
                   apply sep_assoc in H; progress sepsimpl
                 | _ => congruence
                 | _ => ecancel_assumption
                 end.
        { use_sep_assumption.
          cancel.
          admit. }
        { exfalso.
          admit. }
        { exfalso.
          admit. }
        { exfalso.
          admit. }
        { use_sep_assumption.
          cancel. admit. }
        { exfalso.
          admit. }
      Admitted.
    End sep.

    Lemma replace_replace t cond (a1 a2 : alpha) : 
      cond a1 = true ->
      replace (fst (replace t cond a1)) cond a2 =
      replace t cond a2.
    Proof.
      induction t; intros;
        repeat match goal with
               | _ => progress cbn [replace fst snd] in *
               | _ => progress subst
               | _ => progress intuition
               | H : (_,_) = (_,_) |- _ =>
                 inversion H; clear H
               | |- context [match ?x with _ => _ end] =>
                 destruct x eqn:?
               | _ => reflexivity
               | _ => congruence
               end.
   Admitted.
  End proofs.
End Tree.

  
                           
                             
