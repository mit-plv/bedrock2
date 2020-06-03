Require Import Rupicola.Lib.Core.

Ltac boolean_cleanup :=
  repeat match goal with
         | H : _ |- _ =>
           rewrite word.unsigned_of_Z_0 in H
         | H : _ |- _ =>
           rewrite word.unsigned_of_Z_1 in H
         | H : ?x = word.of_Z 0%Z |- _ => subst x
         | H : ?x = word.of_Z 1%Z |- _ => subst x
         | x := word.of_Z 0%Z |- _ => subst x
         | x := word.of_Z 1%Z |- _ => subst x
         | _ => congruence
         end.

Ltac destruct_lists_of_known_length :=
  repeat match goal with
         | H : S _ = S _ |- _ => apply Nat.succ_inj in H
         | H : length ?x = S _ |- _ =>
           destruct x; cbn [length] in H; [ congruence | ]
         | H : length ?x = 0 |- _ =>
           destruct x; cbn [length] in H; [ clear H | congruence]
         end;
  cbn [hd tl] in *.

(* just a wrapper that calls straightline_call + straightline, and also
   destructs output lists *)
Ltac handle_call :=
  ProgramLogic.straightline_call; [ ecancel_assumption | ];
  repeat ProgramLogic.straightline;
  destruct_lists_of_known_length;
  repeat ProgramLogic.straightline.

(* stolen from a bedrock2 example file (LAN9250.v) *)
Ltac split_if solver :=
  lazymatch goal with
    |- WeakestPrecondition.cmd _ ?c _ _ _ ?post =>
    let c := eval hnf in c in
        lazymatch c with
        | Syntax.cmd.cond _ _ _ =>
          letexists; split; [solve[solver]|split]
        end
  end.

Ltac clear_old_seps :=
  match goal with
  | H : sep _ _ ?mem |- context [?mem] =>
    repeat match goal with
           | H' : sep _ _ ?m |- _ =>
             assert_fails (unify m mem); clear H'
           end
  end.

Ltac cleanup :=
  repeat first [ progress cbn [fst snd eq_rect] in *
               | match goal with H : _ /\ _ |- _ => destruct H end
               | match goal with H : exists _, _ |- _ => destruct H end
               | match goal with H : ?x = ?x |- _ => clear H end ].

Ltac sepsimpl_step' :=
  match goal with
  | |- sep (emp _) _ _ => apply sep_emp_l
  | |- sep _ (emp _) _ => apply sep_emp_r
  | |- sep (fun m => emp _ m) _ _ => apply sep_emp_l
  | |- sep _ (fun m => emp _ m) _ => apply sep_emp_r
  | |- sep (Lift1Prop.ex1 _) _ _ => apply sep_ex1_l
  | |- sep _ (Lift1Prop.ex1 _) _ => apply sep_ex1_r
  | |- emp _ _ => split; [ congruence | ]
  end.

Ltac sepsimpl_step :=
  match goal with
  | _ => sepsimpl_step'
  | |- sep (sep _ _) _ _ => apply sep_assoc; sepsimpl_step'
  | |- sep _ (sep _ _) _ => apply sep_comm, sep_assoc; sepsimpl_step'
  | |- sep _ _ _ => apply sep_comm; sepsimpl_step'
  end.

Ltac sepsimpl_in H :=
  match type of H with
  | sep (emp _) _ _ =>
    eapply sep_emp_l in H
  | sep _ (emp _) _ =>
    eapply sep_emp_r in H
  | sep (fun m => emp _ m) _ _ =>
    eapply sep_emp_l in H
  | sep _ (fun m => emp _ m) _ =>
    eapply sep_emp_r in H
  | sep (Lift1Prop.ex1 _) _ _ =>
    eapply sep_ex1_l in H; destruct H
  | sep _ (Lift1Prop.ex1 _) _ =>
    eapply sep_ex1_r in H; destruct H
  end.

Ltac sepsimpl_hyps_step :=
  match goal with
  | H : False |- _ => tauto
  | H : emp _ _ |- _ => cbv [emp] in H; destruct H
  | H : Lift1Prop.ex1 _ _ |- _ => destruct H
  | H : sep (sep ?p ?q) _ _ |- _ =>
    eapply (sep_assoc p q) in H; sepsimpl_in H
  | H : sep _ _ _ |- _ => sepsimpl_in H
  | H : sep _ (sep ?p ?q) _ |- _ =>
    eapply sep_comm, (sep_assoc p q) in H; sepsimpl_in H
  end.

Ltac sepsimpl_hyps :=
  repeat first [ progress cleanup
               | progress sepsimpl_hyps_step ].

Ltac sepsimpl :=
  repeat first [ progress cleanup
               | match goal with |- _ /\ _ => split end
               | progress sepsimpl_step
               | progress sepsimpl_hyps_step ].

(* Notations for program_logic_goal_for_function *)
Local Notation function_t :=
  ((string * (list string * list string * cmd.cmd))%type).
Local Notation functions_t :=
  (list function_t).

(* modified version of program_logic_goal_for_function, in which callee names
  are manually inserted *)
Ltac program_logic_goal_for_function proc callees :=
  let __ := constr:(proc : function_t) in
  let fname := (eval cbv in (fst proc)) in
  let callees := (eval cbv in callees) in
  let spec := lazymatch constr:(_:spec_of fname) with ?s => s end in
  constr:(forall functions : functions_t,
             ltac:(let s := assuming_correctness_of_in
                              callees functions
                              (spec (cons proc functions)) in
                   exact s)).
