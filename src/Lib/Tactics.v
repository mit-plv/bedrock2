Require Import Rupicola.Lib.Core.
Require Import Rupicola.Lib.Notations.

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

Ltac subst_lets_in_goal :=
  repeat match goal with
         | x := _ |- _ =>
           lazymatch goal with
             |- context [x] => subst x end
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
  straightline_call;
  [ ssplit;
    lazymatch goal with
    | |- sep _ _ _ => ecancel_assumption
    | |- exists R, sep _ R _ => eexists; ecancel_assumption
    | _ => idtac
    end
  | cbv [postcondition_for] in *;
    repeat straightline; destruct_lists_of_known_length;
    repeat straightline ].

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
  | |- sep (fun m => Lift1Prop.ex1 _ m) _ _ => apply sep_ex1_l
  | |- sep _ (fun m => Lift1Prop.ex1 _ m) _ => apply sep_ex1_r
  | |- emp _ _ => split; [ congruence | ]
  end.

Ltac sepsimpl_step_no_comm :=
  match goal with
  | _ => sepsimpl_step'
  | |- sep (sep _ _) _ _ => apply sep_assoc; sepsimpl_step'
  | |- sep (sep (sep _ _) _) _ _ =>
    apply sep_assoc; apply sep_assoc; sepsimpl_step'
  end.

Ltac sepsimpl_step :=
  match goal with
  | _ => sepsimpl_step_no_comm
  | |- sep _ (sep _ _) _ =>
    apply sep_comm, sep_assoc; sepsimpl_step_no_comm
  | |- sep _ _ _ => apply sep_comm; sepsimpl_step_no_comm
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
  | sep (fun m => Lift1Prop.ex1 _ m) _ _ =>
    eapply sep_ex1_l in H; destruct H
  | sep _ (fun m => Lift1Prop.ex1 _ m) _ =>
    eapply sep_ex1_r in H; destruct H
  end.

Ltac sepsimpl_hyps_step_no_comm :=
  match goal with
  | H : False |- _ => tauto
  | H : emp _ _ |- _ => cbv [emp] in H; destruct H
  | H : Lift1Prop.ex1 _ _ |- _ => destruct H
  | H : sep (sep ?p ?q) _ _ |- _ =>
    eapply (sep_assoc p q) in H; sepsimpl_in H
  | H : sep (sep (sep ?p ?q) ?r) _ _ |- _ =>
    eapply (sep_assoc (sep p q) r) in H;
    eapply (sep_assoc p q) in H;
    sepsimpl_in H
  | H : sep _ _ _ |- _ => sepsimpl_in H
  end.

Ltac sepsimpl_hyps_step :=
  match goal with
  | _ => sepsimpl_hyps_step_no_comm
  | H : sep _ (sep ?p ?q) _ |- _ =>
    (* reverse order and try simplifying again *)
    eapply sep_comm, (sep_assoc p q) in H;
    sepsimpl_hyps_step_no_comm
  end.

Ltac sepsimpl_hyps :=
  repeat first [ progress cleanup
               | progress sepsimpl_hyps_step ].

Ltac sepsimpl :=
  repeat first [ progress cleanup
               | match goal with |- _ /\ _ => split end
               | progress sepsimpl_step
               | progress sepsimpl_hyps_step ].

(* modification of a few clauses in the straightline tactic (to handle maps
   where put is not computable) *)
Ltac straightline' :=
  match goal with
  | _ => straightline
  | |- exists x, ?P /\ ?Q =>
    let x := fresh x in
    refine (let x := _ in ex_intro (fun x => P /\ Q) x _); split;
    [ solve [ repeat straightline' ] |  ]
  | |- @map.get _ _ ?M _ ?k = Some ?e' =>
    let e := rdelta.rdelta e' in
    is_evar e;
    (match M with | Semantics.locals => idtac end;
     once (let v :=
               multimatch goal with
                 x := context[@map.put _ _ M _ k ?v] |- _ => v end in
           unify e v);
     repeat match goal with
              x := context[map.put _ k _] |- _ => subst x
            end;
     autorewrite with mapsimpl; exact eq_refl)
  | |- @map.get _ _ ?M _ ?k = Some ?e' =>
    let e := rdelta.rdelta e' in
    is_evar e;
    (match M with | Semantics.locals => idtac end;
     once (let v :=
               multimatch goal with
               | H : @map.get _ _ M _ k = Some ?v |- _ => v end in
           unify e v);
     subst_lets_in_goal;
     autorewrite with mapsimpl; eassumption)
  | |- map.get _ _ = Some ?v =>
    let v' := rdelta.rdelta v in
    is_evar v'; change_no_check v with v'; eassumption
  end.


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
