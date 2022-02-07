Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.FE310CSemantics.
Require Import coqutil.Z.Lia.

From bedrock2 Require Import BasicC64Semantics ProgramLogic.
From bedrock2 Require Import Array Scalars Separation.
From coqutil Require Import Word.Interface Map.Interface.

From coqutil.Tactics Require Import letexists.

From coqutil.Tactics Require Import syntactic_unify.
From coqutil.Macros Require Import symmetry.

From coqutil.Tactics Require Import syntactic_unify.
From coqutil.Macros Require Import symmetry.
Require Import coqutil.Datatypes.List.


Section WithParameters.
  Import Syntax BinInt String List.ListNotations ZArith.
  Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

  Definition tf : bedrock_func :=
    ("tf", (["buf"; "len"; "i"; "j"], [], bedrock_func_body:(
      require ( i < len ) else { /*skip*/ };
      store1(buf + i, $0);
      require ( j < len ) else { r = $-1 };
      r = load1(buf + j)
    ))).

    Local Infix "*" := sep : type_scope.
    Local Open Scope sep_scope.
    Local Notation "a [ i ]" := (List.hd _ (List.skipn i a)) (at level 10, left associativity, format "a [ i ]").
    Local Notation "a [: i ]" := (List.firstn i a) (at level 10, left associativity, format "a [: i ]").
    Local Notation "a [ i :]" := (List.skipn i a) (at level 10, left associativity, format "a [ i :]").
    Local Notation bytes := (array ptsto (word.of_Z 1)).
    (* Local Notation word_to_nat x := (Z.to_nat (word.unsigned x)). *)
    Local Infix "+" := word.add.
    Local Infix "+" := word.add.

  Local Instance spec_of_tf : spec_of "tf". refine (fun functions =>
    forall t m buf len bs i j R,
      (sep (array ptsto (word.of_Z 1) buf bs) R) m ->
      word.unsigned len = Z.of_nat (List.length bs) ->
      WeakestPrecondition.call functions "tf" t m [buf; len; i; j]
      (fun T M rets =>
         True)).
  (* word.unsigned i < word.unsigned len -> word.unsigned j < word.unsigned len ->
         rets = [word.of_Z (word.unsigned
                ((bs[:word_to_nat i]++ word.of_Z 0 :: List.tl (bs[word_to_nat i:]))[word_to_nat j]))] *)
  Defined.

  Import SeparationLogic Lift1Prop.

  Goal program_logic_goal_for_function! tf.
  Proof.
    repeat straightline.

    letexists. split; [solve[repeat straightline] |].
    split; [|solve [repeat straightline]]; repeat straightline.
    eapply Properties.word.if_nonzero in H1; rewrite word.unsigned_ltu in H1; eapply Z.ltb_lt in H1.

    simple refine (store_one_of_sep _ _ _ _ _ _ (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ H) _); shelve_unifiable.
    1: (etransitivity; [etransitivity|]); cycle -1; [ | | eapply Proper_sep_iff1; [|reflexivity]; eapply bytearray_index_inbounds]; try ecancel; try blia.

    repeat straightline.

    intros.

    seprewrite_in (symmetry! @array_cons) H2.
    seprewrite_in (@bytearray_index_merge) H2. {
      pose proof Properties.word.unsigned_range i.
      rewrite length_firstn_inbounds; blia.
    }

    letexists.
    split; [solve[repeat straightline]|].
    split; [|solve [repeat straightline]].

    repeat straightline.
    eapply Properties.word.if_nonzero in H3; rewrite word.unsigned_ltu in H3; eapply Z.ltb_lt in H3.

    letexists.
    split. {
      letexists.
      split; repeat straightline.
      letexists; split. {
        eapply load_one_of_sep.
        simple refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ H2).
        (etransitivity; [|etransitivity]); [ | eapply Proper_sep_iff1; [|reflexivity]; eapply bytearray_index_inbounds | ].
        3: ecancel.
        1: ecancel.
        pose proof Properties.word.unsigned_range i.
        pose proof Properties.word.unsigned_range j.
        rewrite List.app_length, length_cons, length_firstn_inbounds, length_skipn.
        all: blia.
    }
    1: subst v1.
    exact eq_refl.
    }

    repeat (straightline; [|..]).

    exact I.
  Qed.

    (* [eseptract] solves goals of the form [state == needle * ?r] by
      "subtracting" [needle] from [state] with the help of decomposition
      hints of the form [a = b * c * d * ...]. [?r] will be instantiated
      with the result of the subtraction "state - needle"; in terms of
      the magic wand operator this tactic simplifies [needle -* state].
      The process is directed by the syntactic form of [needle]:

      1. If [needle] appears syntactically in [state], the equation is
         solved by cancellation.
      2. If [needle] matches a part of a RHS of a decomposition lemma,
         the non-matched part of the RHS is into [r] and the LHS is
         subtracted from the state recursively.
      3. If [needle] is a separating conjunct of multiple clauses, they
         of them will be subtracted separately. *)

    (* TODO: should side conditions be solved before or after recursing?
       - before does not work for arrays -- need to know which array before checking bounds
       - after would mean all leaves of every struct would be explored -- uncontroled search *)

    (* better algorithm might use hints containing:
       - needle pattern
       - state pattern = hint lhs
       - condition when to apply this hint (is needle actually inside pattern?) this might be a judgementally trivial but syntactically informative precondition
       - hint rhs
       on match, only the hint rhs (plus original frame) would be searched for further matches *)
End WithParameters.
