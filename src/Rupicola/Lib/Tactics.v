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

Ltac subst_lets_in_goal :=
  repeat match goal with
         | x := _ |- _ =>
           lazymatch goal with
             |- context [x] => subst x end
         end.

Ltac lift_eexists :=
  repeat
    lazymatch goal with
    | |- Lift1Prop.ex1 _ _ => eexists
    | |- sep (Lift1Prop.ex1 _) _ _ => apply sep_ex1_l
    end.

Ltac destruct_lists_of_known_length :=
  repeat match goal with
         | H : S _ = S _ |- _ => apply Nat.succ_inj in H
         | H : length ?x = S _ |- _ =>
           destruct x; cbn [length] in H; [ congruence | ]
         | H : length ?x = 0%nat |- _ =>
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
  | cbv [postcondition_func postcondition_func_norets] in *;
    repeat straightline; destruct_lists_of_known_length;
    repeat straightline ].

(* stolen from a bedrock2 example file (LAN9250.v) *)
Ltac split_if t :=
  lazymatch goal with
    |- WeakestPrecondition.cmd _ ?c _ _ _ ?post =>
    let c := eval hnf in c in
        lazymatch c with
        | Syntax.cmd.cond _ _ _ =>
          letexists; split; [t|split]
        end
  end.

Ltac clear_old_seps :=
  repeat match goal with
         | H : sep _ _ ?m |- _ =>
           lazymatch goal with
           | |- context [m] => fail
           | _ => clear H
           end
         end.

Ltac cleanup :=
  repeat first [ progress cbn beta iota delta [fst snd eq_rect] in *
               | match goal with
                 | H : _ /\ _ |- _ => destruct H
                 | H : exists _, _ |- _ => destruct H
                 | H : ?x = ?x |- _ => clear H
                 | H : Some _ = Some _ |- _ =>
                   injection H; clear H;
                   let h := fresh H in intros h
                 end ].

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

(* Version of straightline that allows integration of custom solvers *)
Ltac straightline_plus t :=
  first [ straightline | t
          | match goal with
              |- exists x, ?P /\ ?Q =>
              let x := fresh x in
              refine (let x := _ in ex_intro (fun x => P /\ Q) x _); split;
              [ solve [ repeat straightline_plus t ] |  ]
            end ].

(* modification of a few clauses in the straightline tactic (to handle maps
   where put is not computable) *)
Ltac straightline_map_solver :=
  match goal with
  | |- @map.get ?K ?V ?M _ ?k = Some ?e' =>
    let e := rdelta.rdelta e' in
    is_evar e;
    (constr_eq K string; match V with word.rep => idtac end;
     once (let v :=
               multimatch goal with
                 x := context[@map.put _ _ M _ k ?v] |- _ => v end in
           unify e v);
     repeat match goal with
              x := context[map.put _ k _] |- _ => subst x
            end;
     autorewrite with mapsimpl; exact eq_refl)
  | |- @map.get ?K ?V ?M _ ?k = Some ?e' =>
    let e := rdelta.rdelta e' in
    is_evar e;
    (constr_eq K string; match V with word.rep => idtac end;
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

Ltac straightline' := straightline_plus ltac:(solve [straightline_map_solver]).


(* modified version of program_logic_goal_for_function, in which callee names
  are manually inserted *)
Ltac program_logic_goal_for_function proc callees :=
  let __ := constr:(proc : func) in
  let fname := (eval cbv in (fst proc)) in
  (* We do not evaluate callees since in this version they are typically already a value
     and it adds a noticeable performance overhead at declaration and Qed. *)
  let spec := lazymatch constr:(_:spec_of fname) with ?s => s end in
  constr:(forall functions : list func,
             ltac:(let s := assuming_correctness_of_in
                              callees functions
                              (spec (cons proc functions)) in
                   exact s)).

Ltac use_hyp_with_matching_cmd :=
  let H := lazymatch goal with
           | H: context [WeakestPrecondition.cmd _ ?impl]
             |- WeakestPrecondition.cmd _ ?impl _ _ _ _ => H end in
  eapply Proper_cmd;
  [ solve [apply Proper_call]
  | repeat intro | eapply H ].

Ltac push_map_remove :=
  repeat first [ rewrite map.remove_put_diff by congruence
               | rewrite map.remove_put_same ];
  rewrite map.remove_empty.

Ltac term_head x :=
  match x with
  | ?f _ => term_head f
  | _ => x
  end.

Ltac unfold_head term :=
  (** Unfold the head of `term`.
      As a(n unfortunate) side-effect, this function also
      β-reduces the whole term. **)
  let rec loop t :=
      lazymatch t with
      | ?f ?x => let f := unfold_head f in uconstr:(f x)
      | ?f0 => let f0 := (eval red in f0) in uconstr:(f0)
      end in
  let term := loop term in
  let term := type_term term in
  let term := (eval cbv beta in term) in
  term.

Ltac find_app term head :=
  match term with
  | context[head ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9] =>
    constr:(head x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
  | context[head ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8] =>
    constr:(head x0 x1 x2 x3 x4 x5 x6 x7 x8)
  | context[head ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7] =>
    constr:(head x0 x1 x2 x3 x4 x5 x6 x7)
  | context[head ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 ?x6] =>
    constr:(head x0 x1 x2 x3 x4 x5 x6)
  | context[head ?x0 ?x1 ?x2 ?x3 ?x4 ?x5] =>
    constr:(head x0 x1 x2 x3 x4 x5)
  | context[head ?x0 ?x1 ?x2 ?x3 ?x4] =>
    constr:(head x0 x1 x2 x3 x4)
  | context[head ?x0 ?x1 ?x2 ?x3] =>
    constr:(head x0 x1 x2 x3)
  | context[head ?x0 ?x1 ?x2] =>
    constr:(head x0 x1 x2)
  | context[head ?x0 ?x1] =>
    constr:(head x0 x1)
  | context[head ?x0] =>
    constr:(head x0)
  | context[head] =>
    constr:(head)
  | _ => fail "Couldn't find" head "in" term
  end.

Ltac map_to_list' m :=
  let rec loop m acc :=
      match m with
      | map.put ?m ?k ?v =>
        loop m uconstr:((k, v) :: acc)
      | map.empty (key := ?K) (value := ?V) =>
        (* Reverse for compatibility with map.of_list *)
        uconstr:(List.rev_append (A := (K * V)) acc [])
      end in
  loop m uconstr:([]).

Ltac map_to_list m :=
  let l := map_to_list' m in
  let l := (eval cbv [List.rev_acc List.app] in l) in
  l.

Tactic Notation "set_change" uconstr(x) "with" uconstr(y) :=
  (* This tactic uses ‘set’ because ‘change’ sometimes fails to find ‘m’.
     (See the last example of Loops.v for an example). Why? *)
  (let sx := fresh in
   set x as sx; change sx with y; clear sx).

Ltac reify_map m :=
  match type of m with
  | @map.rep _ _ ?M =>
    let b := map_to_list m in
    set_change m with (@map.of_list _ _ M b)
  end.
