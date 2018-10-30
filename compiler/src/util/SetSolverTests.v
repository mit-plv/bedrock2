Require Import compiler.util.Set.

Section Tests.
  Context {E: Type}.
  Context {setInst: SetFunctions E}.

  Ltac t := set_solver_generic E.

  Lemma subset_trans: forall s1 s2 s3,
      subset s1 s2 ->
      subset s2 s3 ->
      subset s1 s3.
  Proof. t. Qed.

End Tests.
