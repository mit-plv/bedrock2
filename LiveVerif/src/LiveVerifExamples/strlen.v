(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import List Lia.

Load LiveVerif.

Import List.

Definition valid_str (str : list Z) : Prop
  := forall i : Z, (0 <= i /\ i < len str) -> str[i] <> 0.
(*
  := 1 <= len str /\ last str 0 = 0 /\
       forall i : nat, Z.of_nat (S (S i)) <= len str -> nth i str 0 <> 0.*)

(* not include 0 in string "value"; use Z here^ *)

Section ListX.
  Context [X : Type].
  Context {inh : inhabited X}.
  

Lemma lget_in_first : forall (l1 l2 : list X) (i : Z),
    i < len l1 -> List.get (l1 ++ l2) i = List.get l1 i.
Proof.
  intros. unfold List.get. destruct (i <? 0) eqn:E. reflexivity.
  apply app_nth1. lia.
Qed.

Lemma lget_in_second : forall (l1 l2 : list X) (i : Z),
    len l1 <= i -> List.get (l1 ++ l2) i = List.get l2 (i - len l1).
Proof.
  intros. unfold List.get.
  replace (i <? 0) with false; [ | lia ].
  replace (i - len l1 <? 0) with false; [ | lia ].
  Search nth "++".
  replace (Z.to_nat (i - len l1)) with (Z.to_nat i - Z.to_nat (len l1))%nat; [ | lia ].
  replace (Z.to_nat (len l1)) with (Datatypes.length l1); [ | lia ].
  apply app_nth2. lia.
Qed.

Lemma lget_cons_from : forall (l : list X) (i : Z),
  0 <= i -> i < len l -> l[i] :: l[i + 1:] = l[i:].
Proof.
  intros. unfold List.from. unfold List.get. assert (Hpos: i <? 0 = false). lia.
  rewrite Hpos. rewrite Z2Nat.inj_add; [ | lia | lia ]. change (Z.to_nat 1) with (1%nat).
  remember (Z.to_nat i) as n.
  Search (skipn) (_ :: _).
  erewrite <- (List.firstn_nth_skipn) with (i := 0%nat). 
  replace (n + 1)%nat with (S n); [ | lia ]. rewrite List.skipn_skipn.
  rewrite List.nth_skipn. simpl. f_equal. f_equal. lia. rewrite skipn_length. lia.
Qed.

End ListX.

Check (_ : inhabited Z).

(* PROBLEM HERE: step doesn't know how to prove (inhabited Z)
Lemma lget_in_second : forall (X : Type) {inh : inhabited X} (l1 l2 : list X) (i : Z),
    inhabited X -> len l1 <= i -> List.get (l1 ++ l2) i = List.get l2 (i - len l1).
Proof.
  intros. unfold List.get.
  replace (i <? 0) with false; [ | lia ].
  replace (i - len l1 <? 0) with false; [ | lia ].
  Search nth "++".
  replace (Z.to_nat (i - len l1)) with (Z.to_nat i - Z.to_nat (len l1))%nat; [ | lia ].
  replace (Z.to_nat (len l1)) with (Datatypes.length l1); [ | lia ].
  apply app_nth2. lia.
Qed.
 *)

#[export] Instance spec_of_strlen: fnspec :=                               .**/
uintptr_t strlen(uintptr_t s) /**#
  ghost_args := (sli : list Z) (R: mem -> Prop);
                requires t m := sep (array (uint 8) (len sli + 1) (sli ++ [|0|]) s) R m /\ len sli + 1 <= 2 ^ 32 /\
                                  valid_str sli;
  ensures t' m' retv := t' = t /\
                          sep (array (uint 8) (len sli + 1) (sli ++ [|0|]) s) R m' /\
                          \[retv] = len sli
                     #**/ /**.
Derive strlen SuchThat (fun_correct! strlen) As strlen_ok.                 .**/
{                                                                     /**. .**/
  uintptr_t p = s;                                                    /**.
  let h := constr:(#(valid_str sli)) in move h after t.
  unfold valid_str in *.
  loop invariant above p.
  prove (\[p ^- s] <= len sli).
  delete #(p = s).                                                     .**/
  while (load8(p) != 0) /* decreases (s ^+ /[len sli] ^- p) */ {       /**.
                                                                       .**/
    p = p + 1;                                                        /**. .**/
  }                                                                   /*?.

  step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step.
  { assert (\[p' ^- s] = len sli -> (sli ++ [|0|])[\[p' ^- s]] = 0). step.
    rewrite lget_in_second. rewrite H1. step. step. lia. zify_hyps. step. }
  step. step.
  { replace (sli[:\[p' ^- s]]) with ((sli ++ [|0|])[:\[p' ^- s]]). rewrite lget_cons_from. rewrite <- List.split_at_index. step. step. step. step. step. step. step. step. step. step. }
  subst v. subst p.
  { assert (\[p' ^- s] = len sli -> (sli ++ [|0|])[\[p' ^- s]] = 0). { step.
    rewrite lget_in_second. rewrite H0. step. step. lia. } zify_hyps. step. }
  .**/
  return p - s;                                                           /**. .**/
}                                                                     /*?.
  step. step. step. step. step. step. step. step.
  { assert (\[p ^- s] < len sli -> (sli ++ [|0|])[(\[p ^- s])] <> 0). { step.
    rewrite lget_in_first. apply Hp2. step. step. step. step. } step. }
  step. step.
  { replace (sli[:\[p ^- s]]) with ((sli ++ [|0|])[:\[p ^- s]]). rewrite lget_cons_from. rewrite <- List.split_at_index. step. step. step. step. step. step. step. step. step. step. }
Qed.

End LiveVerif. Comments .**/ //.
(* assert (subrange p 1 s (len sli * 1)). { unfold subrange. unfold valid_str in *. zify_goal; xlia zchecker. subst p. bottom_up_simpl_in_goal. ZnWords_pre. destruct H4. ZnWords.*)
