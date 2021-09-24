Require Import bedrock2.Map.SeparationLogic.

(*TODO: this should make its way into bedrock directly at some point *)
Require Import Coq.Classes.Morphisms.
Require Import bedrock2.Lift1Prop.
Require Coq.Lists.List.
Require Import coqutil.sanity coqutil.Decidable coqutil.Tactics.destr.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Import Map.Interface.map Map.Properties.map.

Require Import coqutil.Tactics.syntactic_unify coqutil.Tactics.rdelta.

(* Everything here is copied from bedrock2.Map.SeparationLogic and modified to work with implications *)
Section SepProperties.
  Context {key value} {map : map key value} {ok : ok map}.
  Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.
  Local Open Scope sep_scope.

  Local Infix "++" := app. Local Infix "++" := app : list_scope.
  Let nth n xs := hd (emp(map:=map) True) (skipn n xs).
  Let remove_nth n (xs : list (map -> Prop)) :=
    (firstn n xs ++ tl (skipn n xs)).

  (* Need this to be restated to use nth in the type*)
  Definition seps_nth_to_head : forall n xs, Lift1Prop.iff1 (sep (nth n xs) (seps (remove_nth n xs))) (seps xs) :=
    seps_nth_to_head.
  
  Lemma cancel_seps_at_indices i j xs ys
        (Hij : Lift1Prop.impl1 (nth i xs) (nth j ys))
        (Hrest : Lift1Prop.impl1 (seps (remove_nth i xs)) (seps (remove_nth j ys)))
    : Lift1Prop.impl1 (seps xs) (seps ys).
  Proof.
    rewrite <-(seps_nth_to_head i xs), <-(seps_nth_to_head j ys).
    rewrite Hij, Hrest.
    exact (reflexivity _).
  Qed.
  
End SepProperties.
  
  (* leaves two open goals:
   1) equality between left sep clause #i and right sep clause #j
   2) updated main goal *)
Ltac cancel_seps_at_indices i j :=
  lazymatch goal with
  | |- Lift1Prop.impl1 (seps ?LHS) (seps ?RHS) =>
    simple refine (cancel_seps_at_indices i j LHS RHS _ _);
    cbn [firstn skipn app hd tl]
  end.

Create HintDb ecancel_impl discriminated.
Hint Extern 1 => exact (fun m x => x) : ecancel_impl.

(*TODO: performance*)
Ltac find_implication xs y :=
  multimatch xs with
  | cons ?x _ =>
    let H := fresh in
    constr:(O)
  | cons _ ?xs => let i := find_implication xs y in constr:(S i)
  end.


(*TODO: performance. I've replaced the deltavar stuff with heavier operations  *)
Ltac ecancel_step ::=
      let RHS := lazymatch goal with |- Lift1Prop.impl1 _ (seps ?RHS) => RHS end in
      let jy := index_and_element_of RHS in (* <-- multi-success! *)
      let j := lazymatch jy with (?i, _) => i end in
      let y := lazymatch jy with (_, ?y) => y end in
      (* For implication, we don't want to touch RHS evars 
         until everything else is solved.
         Makes sure j doesn't point to an evar
       *)
      (*TODO: I already have y, simplify this*)
      assert_fails (idtac; is_evar y);      
      let LHS := lazymatch goal with |- Lift1Prop.impl1 (seps ?LHS) _ => LHS end in
      let i := find_implication LHS y in (* <-- multi-success! *)
      cancel_seps_at_indices i j; [solve [auto 1 with ecancel_impl]|].

(*TODO: should I use deltavar here too?*)
(*TODO: this assumes that the goal has (at most or exactly?) 1 evar predicate.
  Test it on 0, 2 evars and adapt as necessary
*)
Ltac ecancel :=
  cancel; repeat ecancel_step; (solve [ exact (fun m x => x) ]).

 Ltac ecancel_assumption_impl :=
    multimatch goal with
    | |- ?PG ?m1 =>
      multimatch goal with
      | H: ?PH ?m2
        |- _ =>
        syntactic_unify_deltavar m1 m2;
        refine (Morphisms.subrelation_refl Lift1Prop.impl1 PH PG _ m1 H); clear H;
        cbn[seps];(*TODO: why is this needed?*)
        solve[ecancel]
      end
    end.

 (*
   To use this version of ecancel_assumption with Rupicola, add the following line to your file:
   Ltac ecancel_assumption ::=  ecancel_assumption_impl.
*)
