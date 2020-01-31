Require Import Coq.ZArith.ZArith.
Require Import coqutil.Map.Interface.
Require Import coqutil.Z.Lia.
Require Import compiler.FlatImp.
Require Import compiler.FlatToRiscvCommon.
Require Import compiler.FlatToRiscvFunctions.
Require Import compiler.Simp.

Local Open Scope Z_scope.

Section FitsStack.
  Context {p: FlatToRiscvCommon.parameters}.

  Definition stack_usage_impl(outer_rec: env -> stmt Z -> option Z)(e: env): stmt Z -> option Z :=
    fix inner_rec s :=
      match s with
      | SLoad _ _ _ | SStore _ _ _ | SLit _ _ | SOp _ _ _ _ | SSet _ _ | SSkip | SInteract _ _ _ => Some 0
      | SIf _ s1 s2 | SLoop s1 _ s2 | SSeq s1 s2 =>
        match inner_rec s1, inner_rec s2 with
        | Some u1, Some u2 => Some (Z.max u1 u2)
        | _, _ => None
        end
      | SCall binds fname args =>
        match map.get e fname with
        | Some (argnames, retnames, body) =>
          match outer_rec (map.remove e fname) body with
          | Some u => Some (framelength (argnames, retnames, body) + u)
          | None => None
          end
        | None => None
        end
    end.

  Fixpoint stack_usage_rec(env_size_S: nat): env -> stmt Z -> option Z :=
    match env_size_S with
    | O => fun _ _ => None
    | S env_size => stack_usage_impl (stack_usage_rec env_size)
    end.

  Definition count_funs: env -> nat := map.fold (fun acc _ _ => S acc) O.

  (* returns the number of stack words needed to execute f_entrypoint (which must have no args
     and no return values), None if a function not in funimpls is called or a function is recursive *)
  Definition stack_usage_of_fun(funimpls: env)(f_entrypoint: String.string): option Z :=
    stack_usage_rec (S (count_funs funimpls)) funimpls (SCall nil f_entrypoint nil).

  Definition stack_usage(funimpls: env): option Z :=
    map.fold (fun res fname '(argnames, retnames, body) =>
                match res with
                | Some res => match argnames, retnames with
                              | nil, nil => match stack_usage_of_fun funimpls fname with
                                            | Some res' => Some (Z.max res res')
                                            | None => None
                                            end
                              | _, _ => Some res
                              end
                | None => None
                end)
             (Some 0)
             funimpls.

  Lemma fits_stack_monotone: forall e z1 s,
      fits_stack z1 e s -> forall z2, z1 <= z2 -> fits_stack z2 e s.
  Proof.
    induction 1; intros; econstructor; eauto; try blia.
    eapply IHfits_stack. blia.
  Qed.

  Lemma stack_usage_rec_correct: forall n e s z,
      stack_usage_rec n e s = Some z ->
      fits_stack z e s.
  Proof.
    induction n; intros.
    - simpl in H. discriminate.
    - simpl in H.
      revert z H.
      induction s; intros; simpl in H; simp.
      all: try (constructor; eauto using fits_stack_monotone, Z.le_max_l, Z.le_max_r; blia).
      econstructor. 1: eassumption.
      eapply IHn. Fail rewrite E0. (* PARAMRECORDS *) etransitivity. 1: exact E0.
      f_equal. unfold framelength. blia.
  Qed.

End FitsStack.
