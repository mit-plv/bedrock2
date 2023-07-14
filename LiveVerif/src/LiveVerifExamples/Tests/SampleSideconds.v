Require Import LiveVerif.LiveVerifLib.

Ltac standalone_solver_step :=
  first
      [ (* tried first because it also solves some goals of shape (_ = _) and (_ /\ _) *)
        zify_hyps; zify_goal; xlia zchecker
      | (* manually chosen set of safe_implication steps: *)
        lazymatch goal with
        | |- ?xs ++ ?ys1 = ?xs ++ ?ys2 => f_equal
        | |- ?xs1 ++ ?ys = ?xs2 ++ ?ys => f_equal
        end
      (* from step_hook in tree_set: *)
      | lazymatch goal with
        | |- ?A \/ ?B =>
            tryif (assert_succeeds (assert (~ A) by (zify_hyps; zify_goal; xlia zchecker)))
            then right else
            tryif (assert_succeeds (assert (~ B) by (zify_hyps; zify_goal; xlia zchecker)))
            then left else fail
        end
      | lazymatch goal with
        | H: _ \/ _ |- _ =>
            destruct H; try (exfalso; congruence);
            [ ]
        end
      | lazymatch goal with
        | |- ?P /\ ?Q =>
            split
        | |- _ = _ =>
            careful_reflexivity_step_hook
        | |- impl1 ?lhs ?rhs =>
            careful_reflexivity_step_hook
        | |- iff1 _ _ =>
            careful_reflexivity_step_hook
        | |- forall _, _ =>
            intros
        end
      | solve [intuition idtac]
    ].

Ltac t := repeat standalone_solver_step.

(* TODO investigate why standalone_solver_step is not as powerful as step *)

Load LiveVerif.

Goal forall (b n : word) (bs : list Z),
 len bs = \[n] ->
 forall (i : word),
 \[b] < 2 ^ 8 -> i = /[0] -> List.repeatz \[b] \[i] ++ bs[\[i]:] = bs.
Proof. t. Qed.

Goal forall (a b r : word) (c : bool),
 c = word.ltu a b ->
 r = (if c then a else b) -> \[a] < \[b] /\ r = a \/ \[b] <= \[a] /\ r = b.
Proof. t. Qed.

Goal forall (a b c : word) (r : word),
 \[a] < \[b] /\ r = a \/ \[b] <= \[a] /\ r = b ->
 forall (s : word),
 \[r] < \[c] /\ s = r \/ \[c] <= \[r] /\ s = c ->
 \[s] = Z.min \[a] (Z.min \[b] \[c]).
Proof. t. Qed.

Goal forall (l: word),
 l <> /[0] ->
 \[l] = 0 ->
 False.
Proof. t. Qed.

Goal forall (l: word) (z: Z),
 l <> /[z] ->
 \[l] = z ->
 False.
Proof. t. Qed.

Goal forall (l : list word) (lDone lTodo : list word),
 forall (x : word) (l' : list word),
 lTodo = x :: l' ->
 l = lDone ++ lTodo ->
 l = (lDone ++ [|x|]) ++ l'.
Proof. t. Qed.

Goal forall (p v : word) (t t0 : trace) (s : Z -> Prop) (res : word),
 res = /[0] ->
 forall a : word,
 a = p ->
 t0 = t ->
 (forall x : Z, ~ s x) ->
 a = /[0] ->
 \[a] = 0 - 2 ^ 32 * (0 / 2 ^ 32) ->
 ~ s \[v] ->
 (\[res] = 1 /\ s \[v] \/ \[res] = 0 /\ ~ s \[v]) /\ t0 = t.
Proof. t. Qed.

Goal forall (fib: word -> word) (n : word),
 n <> /[0] ->
 forall (v : Z) (i' a' : word),
 a' = fib (i' ^- /[1]) ->
 forall t a b i : word,
 v = \[n] - \[i'] ->
 1 <= \[i'] <= \[n] ->
 \[i'] < \[n] ->
 a = fib i' ->
 t = a' ^+ fib i' -> b = t -> i = i' ^+ /[1] ->
 a = fib (i ^- /[1]).
Proof.
  t. unfold don't_know_how_to_prove. subst i. bottom_up_simpl_in_goal. reflexivity.
Qed.

Goal forall (fib: word -> word) (n : word),
 n <> /[0] ->
 forall (v : Z) (i a : word),
 a = fib (i ^- /[1]) ->
 forall b : word,
 b = fib i ->
 v = \[n] - \[i] ->
 1 <= \[i] <= \[n] ->
 \[n] <= \[i] ->
 b = fib n.
Proof.
  t. unfold don't_know_how_to_prove. replace i with n by ZnWords. reflexivity.
Qed.

Goal forall (in0 in1 in2 : Z) (w0 : word),
 w0 = /[in0] ->
 forall (w2'' w1 w2 : word) (c c' : bool),
 c' = negb (word.ltu /[in0] /[in1]) && negb (word.ltu /[in2] /[in1]) ->
 c = negb (word.ltu /[in0] /[in2]) && negb (word.ltu /[in1] /[in2]) ->
 w2'' = (if c then /[in0] else /[in2]) ->
 0 <= in0 < 2 ^ 32 ->
 w1 = (if c' then /[in0] else /[in1]) ->
 w2 = (if c' then /[in2] else w2'') ->
 forall (m m0 m2 m1 m4 : mem) (c0 : bool),
 c0 = word.ltu w2 w1 ->
 0 <= in1 < 2 ^ 32 ->
 0 <= in2 < 2 ^ 32 ->
 (if c' then in1 else if c then in2 else in0) <=
   \[if c0 then w2 else w1] <= \[if c0 then w1 else w2].
Proof. t. Qed.

Goal forall (v : word) (s0 : Z -> Prop) (a' : word) (res a : word) (v1 : Z),
 s0 v1 ->
 (forall x : Z, ~ (s0 x /\ x < v1)) ->
 res = /[0] ->
 a' <> /[0] ->
 forall here : word,
 here = /[v1] ->
 \[v] < v1 ->
 0 <= v1 < 2 ^ 32 ->
 a = /[0] ->
 ~ (s0 \[v] /\ \[v] < v1) ->
 \[res] = 0 /\ ~ s0 \[v].
Proof. t. Qed.

Goal forall (v : word) (t : trace) (s0 : Z -> Prop) (a' : word) (res a : word) (v1 : Z),
 s0 v1 ->
 (forall x : Z, ~ (s0 x /\ x < v1)) ->
 res = /[0] ->
 a' <> /[0] ->
 forall here : word,
 here = /[v1] ->
 \[v] < v1 ->
 0 <= v1 < 2 ^ 32 ->
 a = /[0] ->
 ~ (s0 \[v] /\ \[v] < v1) ->
 (\[res] = 1 /\ s0 \[v] \/ \[res] = 0 /\ ~ s0 \[v]) /\ t = t.
Proof. t. Qed.
