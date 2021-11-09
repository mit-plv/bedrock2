Require Import Rupicola.Lib.Api.

Section Tree.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Notation address := word.

  Inductive annotation :=
  | Borrowed (a: address)
  | Reserved (a: address)
  | Owned.

  Notation Annotated alpha := (annotation * alpha)%type.

  Inductive tree {alpha : Type} :=
  | Empty : tree
  | Node : alpha -> tree -> tree -> tree.

  Arguments tree : clear implicits.

  Section defs.
    Context {alpha : Type}.

    Fixpoint owned (t : tree alpha)
      : tree (Annotated alpha) :=
      match t with
      | Empty => Empty
      | Node a l r => Node (Owned, a) (owned l) (owned r)
      end.

    Definition setRoot (t : tree alpha) (a : alpha)
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
      Context {Alpha : word -> alpha -> mem -> Prop}
              {word_size_in_bytes : Z}.

      Local Notation word_offset :=
        (word.of_Z word_size_in_bytes).

      Definition AnnotatedAlpha
                 (addr : word)
                 (x : Annotated alpha)
        : mem -> Prop :=
        match x with
        | (Borrowed p, _) => emp (addr = p)
        | (Reserved p, a) => sep (Alpha addr a) (emp (addr = p))
        | (Owned, a) => Alpha addr a
        end.

      Fixpoint Tree
               (addr : word)
               (t : tree (Annotated alpha))
        : mem -> Prop :=
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
    Lemma owned_setRoot_comm t (a : alpha) :
      setRoot (owned t) (Owned, a) = owned (setRoot t a).
    Proof. destruct t; reflexivity. Qed.

    Definition lift {T} (f : alpha -> T) (x : Annotated alpha) :=
      f (snd x).

    Lemma owned_replace_comm t cond (a : alpha) :
      replace (owned t) (lift cond) (Owned, a)
      = (owned (fst (replace t cond a)),
         snd (replace t cond a)).
    Proof.
      induction t; cbn [replace owned];
        try reflexivity.
      repeat match goal with
             | _ => progress subst
             | _ => progress unfold lift in *
             | _ => progress cbn [owned fst snd] in *
             | H : (_,_) = (_,_) |- _ =>
               inversion H; clear H
             | |- context [match ?x with _ => _ end] =>
               destruct x eqn:?
             | _ => reflexivity
             end.
    Qed.

    Section sep.
      Context
        {word_ok : word.ok word} {mem_ok : map.ok mem}
        {locals_ok : map.ok locals}
        {env_ok : map.ok env}
        {ext_spec_ok : Semantics.ext_spec.ok ext_spec}
        {Alpha : word -> alpha -> mem -> Prop}
        {word_size_in_bytes : Z}.

      Local Notation word_offset :=
        (word.of_Z word_size_in_bytes).
      Local Notation Tree :=
        (@Tree _ Alpha word_size_in_bytes).

      Lemma lookup_replace t cond :
        forall a olda pt pa R mem,
          sep (sep (Tree pt t) (Alpha pa a)) R mem ->
          lookup t cond = Some (Borrowed pa, olda) ->
          sep (Tree pt (fst (replace t cond (Owned, a)))) R mem.
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
        1: use_sep_assumption; cancel.
        2: exfalso.
        3: exfalso.
        4: exfalso.
        5: use_sep_assumption; cancel.
        6: exfalso.
      Abort.
    End sep.

    Lemma replace_replace t cond (a1 a2 : alpha) :
      cond a1 = true ->
      replace (fst (replace t cond a1)) cond a2 =
      replace t cond a2.
    Proof.
      (* induction t; intros; *)
      (*   repeat match goal with *)
      (*          | _ => progress cbn [replace fst snd] in * *)
      (*          | _ => progress subst *)
      (*          | _ => progress intuition *)
      (*          | H : (_,_) = (_,_) |- _ => *)
      (*            inversion H; clear H *)
      (*          | |- context [match ?x with _ => _ end] => *)
      (*            destruct x eqn:? *)
      (*          | _ => reflexivity *)
      (*          | _ => congruence *)
      (*          end. *)
    Abort.

    Section borrowing.
      Context {Alpha : word -> alpha -> mem -> Prop}
              {word_size_in_bytes : Z}.

      Open Scope nat_scope.
      Definition a (n: nat) := n + 1.
      Definition b (n: nat) := a n + 1.
      Definition c (n: nat) := b n + 1.

      Hint Unfold a : test.
      Hint Unfold b : test.
      Hint Unfold c : test.

      (* Goal c 3 = 5. *)
      (*   autounfold with test. *)


      (* Lemma borrow_reserved : *)
      (*   forall addr t cond pa a, *)
      (*     find t (lift cond) = Some (Reserved pa, a) -> *)
      (*     Tree (Alpha := Alpha) addr t -> *)
      (*     sep (Alpha a) (Tree addr (replace t (lift cond) (Borrowed pa, a))). *)
      (* Abort. *)


      (* Lemma owned_replace_comm t cond (a : alpha) : *)
      (*   replace (owned t) (lift cond) (Owned, a) *)
      (*   = (owned (fst (replace t cond a)), *)
      (*       snd (replace t cond a)). *)
      (* Abort. *)
    End borrowing.
  End proofs.
End Tree.
