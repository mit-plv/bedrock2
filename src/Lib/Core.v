Require Export Coq.Strings.String.
Require Export Coq.Numbers.DecimalString.
Require Export Coq.Lists.List.
Require Export Coq.ZArith.ZArith.
Require Export Coq.micromega.Lia.
Require Export bedrock2.Array.
Require Export bedrock2.Map.Separation.
Require Export bedrock2.ProgramLogic.
Require Export bedrock2.Map.SeparationLogic.
Require Export bedrock2.Scalars.
Require Export bedrock2.Syntax.
Require Export bedrock2.WeakestPreconditionProperties.
Require Export coqutil.dlet.
Require Export coqutil.Map.Interface coqutil.Map.Properties coqutil.Map.SortedList.
Require Export coqutil.Z.PushPullMod.
Require Export coqutil.Tactics.Tactics.
Require Export coqutil.Tactics.letexists.
Require Export coqutil.Word.Interface coqutil.Word.Properties.
Require bedrock2.ProgramLogic.

Open Scope string_scope.
Export ListNotations.

Declare Scope sep_scope.
Delimit Scope sep_scope with sep.
Infix "*" := (sep) : sep_scope.

Set Nested Proofs Allowed.

Notation word := Semantics.word.

(* FIXME instead of cbn [fst snd], use simpl never hints in the sep case *)
Arguments Semantics.word : simpl never.

Notation address := word (only parsing).

Definition bedrock_func : Type :=
  string * (list string * list string * cmd).
Coercion name_of_func (f : bedrock_func) := fst f.

Hint Rewrite @map.get_put_diff @map.get_put_same @map.put_put_same
     using (typeclasses eauto || congruence) : mapsimpl.


(* TODO: should move upstream to coqutil *)
Module map.
  Section __.
    Context {key value} {map : map.map key value}
            {map_ok : map.ok map}
            {key_eqb}
            {key_eq_dec :
               forall x y : key, BoolSpec (x = y) (x <> y) (key_eqb x y)}.

    Lemma put_put_diff_comm k1 k2 v1 v2 m :
      k1 <> k2 ->
      map.put (map.put m k1 v1) k2 v2 = map.put (map.put m k2 v2) k1 v1.
    Proof.
      intros. apply map.map_ext. intros.
      rewrite !map.get_put_dec;
        repeat match goal with |- context [key_eqb ?x ?y] =>
                               destr (key_eqb x y) end;
        congruence.
    Qed.

    Lemma put_noop k v m :
      map.get m k = Some v -> map.put m k v = m.
    Proof.
      intros. apply map.map_ext. intros.
      rewrite !map.get_put_dec;
        repeat match goal with |- context [key_eqb ?x ?y] =>
                               destr (key_eqb x y) end;
        congruence.
    Qed.
  End __.
End map.
