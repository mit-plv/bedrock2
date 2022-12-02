(* -*- eval: (load-file "../live_verif_setup.el"); -*- *)
Require Import bedrock2Examples.LiveVerif.LiveVerifLib. Load LiveVerif.

#[export] Instance spec_of_u_min: fnspec :=                                     .**/

uintptr_t u_min (uintptr_t a, uintptr_t b) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := R m;
  ensures t' m' retv := t' = t /\ R m' /\
      (\[a] < \[b] /\ retv = a \/ \[b] <= \[a] /\ retv = b) #**/           /**.
Derive u_min SuchThat (fun_correct! u_min) As u_min_ok.                         .**/
{                                                                          /**. .**/
  uintptr_t r = 0;                                                         /**. .**/
  if (a < b) {                                                             /**. .**/
    r = a;                                                                 /**. .**/
  } else {                                                                 /**. .**/
    r = b;                                                                 /**. .**/
  }                                                                        /**. .**/
  return r;                                                                /**. .**/
}                                                                          /**.
Defined.

Lemma nth_function_correct: forall fs n specs spec default,
    List.nth n specs default = spec ->
    functions_correct fs specs ->
    spec fs.
Proof.
  unfold functions_correct. intros.
  Search List.Forall List.nth.
Admitted.

Definition minl: list Z -> Z := List.fold_right Z.min 0.

#[export] Instance spec_of_u_min3: fnspec :=                                    .**/

uintptr_t u_min3 (uintptr_t a, uintptr_t b, uintptr_t c) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := R m;
  ensures t' m' retv := t' = t /\ R m' /\
      \[retv] = minl [| \[a]; \[b]; \[c] |] #**/                           /**.
Derive u_min3 SuchThat (fun_correct! u_min3) As u_min3_ok.                      .**/
{                                                                          /**.
(*   uintptr_t r = u_min(a, b); *)
  eapply wp_call.
  { ltac1:(
    let fname := constr:("u_min") in
    let s := lazymatch constr:(_ : ProgramLogic.spec_of fname) with ?sp => sp end in
    let s' := eval unfold s in s in
    let new_callee_list := open_constr:(cons s _) in
    lazymatch goal with
    | H: functions_correct ?fs ?l |- _ =>
        let callee_list_evar := strip_conss l in
        unify callee_list_evar new_callee_list
    end;

    idtac s).
    eapply (nth_function_correct _ O) in H. 2: cbn [List.nth]; reflexivity.
    unfold spec_of_u_min in H.
    eapply H.
  }
Abort.

End LiveVerif. Comments .**/ //.
