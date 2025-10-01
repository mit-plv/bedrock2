From Coq Require Import String List.
From coqutil.Tactics Require Import Tactics letexists eabstract rdelta reference_to_string ident_of_string.
From coqutil Require Import Macros.ident_to_string Map.Interface Datatypes.ListSet.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.Loops.
Require Import bedrock2.Map.SeparationLogic bedrock2.Scalars.

Definition spec_of (procname:String.string) := Semantics.env -> Prop.
Existing Class spec_of.

Module Import Coercions.
  Export coqutil.Map.Separation.
  Import Map.Interface Word.Interface BinInt.
  Coercion Z.of_nat : nat >-> Z.
  Coercion word.unsigned : word.rep >-> Z.
End Coercions.

Goal True.
  assert_succeeds epose (fun k v M (m : @Interface.map.rep k v M) => m _).
Abort.

Require Import Ltac2.Ltac2.

Local Ltac2 rec splitcmd (cmd : constr) : unit :=
  match! cmd with
    | cmd.seq ?cmd1 ?cmd2 =>
        set (cmd.seq $cmd1 $cmd2) in *; splitcmd cmd1; splitcmd cmd2
    | cmd.cond ?expr ?cmd1 ?cmd2 => set (cmd.cond $expr $cmd1 $cmd2) in *; splitcmd cmd1; splitcmd cmd2
    | cmd.while ?expr ?cmd => set (cmd.while $expr $cmd) in *; splitcmd cmd
    | _ => ()
  end.

Local Ltac2 Notation "instance_of" type(constr) :=
  lazy_match! Ltac2.Constr.pretype (preterm:(_ : $type)) with ?instance => instance end.

(* Unfold x until it's not a const, used to unfold layered definitions hiding the function body. *)
Local Ltac2 rec unfold_const x :=
  if Bool.neg (Constr.is_const x) then x else
    let ref := reference_to_string.reference_of_constr x in
    match! eval cbv delta [$ref] in $x with ?x => unfold_const x
  end.

Local Ltac2 function_body (proc : constr) : constr :=
  let unfolded := unfold_const proc in
  match! unfolded with (_, _, ?fbody) => fbody end.

(* TODO prevent duplicates. *)
Local Ltac2 rec callee_specs (cmd : constr) : constr list :=
  match! cmd with
    | cmd.cond _ ?c1 ?c2  => List.append (callee_specs c1) (callee_specs c2)
    | cmd.seq ?c1 ?c2 => List.append (callee_specs c1) (callee_specs c2)
    | cmd.while _ ?c => callee_specs c
    | cmd.stackalloc _ _ ?c => callee_specs c
    | cmd.call _ ?f _ => [instance_of (spec_of $f)]
    | cmd.skip => []
    | cmd.set _ _ => []
    | cmd.unset _ => []
    | cmd.store _ _ _ => []
    | cmd.interact _ _ _ => []
    | _ => Control.throw (Invalid_argument (Some (Message.concat
        (Message.of_string "Failed to recurse into the following command, consider reducing it before calling program_logic_goal_for: ")
        (Message.of_constr cmd))))
  end.

(* Extracts all "callees", that is functions called by proc and creates a goal of the form "specs of callees -> spec of proc". *)
Local Ltac2 program_logic_goal_for_function (proc : constr) : unit := 
  let fname := constr_string_basename_of_constr_reference proc in
  let fname_spec := instance_of (spec_of $fname) in
  let fbody := function_body proc in
  let goal := (fun (functions : constr) =>
    List.fold_right (fun premise_spec conclusion => '(($premise_spec $functions) -> $conclusion)) (callee_specs fbody) '($fname_spec $functions)) in
  exact (forall (functions : @map.rep _ _ Semantics.env) (EnvContains : map.get functions $fname = Some $proc),
    ltac2:(let g := goal &functions in exact $g)
  ).

Set Default Proof Mode "Classic".

Definition program_logic_goal_for (_ : Syntax.func) (P : Prop) := P.

Notation "program_logic_goal_for_function! proc" := (program_logic_goal_for proc ltac2:(
   program_logic_goal_for_function (Ltac2.Constr.pretype proc)))
  (at level 10, only parsing).

(* Users might want to override this with
     Ltac normalize_body_of_function f ::= Tactics.rdelta.rdelta f.
   in case cbv does more simplification than desired. *)
Ltac normalize_body_of_function f := eval cbv in f.

(* Splits up the function f and extracts its commands line by line into hypothesis. *)
Ltac bind_body_of_function f_ :=
  let f := normalize_body_of_function f_ in
  let fbody := open_constr:(_) in
  let funif := open_constr:((_, _, fbody)) in
  unify f funif;
  let go_split := ltac2:(fbody |-
    let fbody_value := Option.get (Ltac1.to_constr fbody) in
    splitcmd fbody_value) in
  change f_ with f;
  go_split fbody; intros.

(* note: f might have some implicit parameters (eg a record of constants) *)
Ltac enter f :=
  cbv beta delta [program_logic_goal_for];
  bind_body_of_function f;
  lazymatch goal with |- ?s ?p => let s := rdelta s in change (s p); cbv beta end.

Require coqutil.Map.SortedList. (* special-case eq_refl *)

(* Destructing section variables is unpredictable COQBUG(6826).
    To avoid destructing them, we detect whether a variable is a section variable.
    For lack of better functions to do so, consider a hypothesis section variable
    if it does not disappear after calling destruct on it while it's in the goal.   *)
Ltac is_context_variable H :=
  assert_succeeds (exfalso; clear -H; assert(H = H);
    let A := fresh in let B := fresh in destruct H as [A B]; pose H).

Ltac straightline_cleanup :=
  match goal with
  (* TODO remove superfluous _ after .rep, but that will break some proofs that rely on
     x not being cleared to instantiate evars with terms depending on x *)
  | x : Word.Interface.word.rep _ |- _ => clear x
  | x : Init.Byte.byte |- _ => clear x
  | x : Semantics.trace |- _ => clear x
  | x : Syntax.cmd |- _ => clear x
  | x : Syntax.expr |- _ => clear x
  | x : coqutil.Map.Interface.map.rep |- _ => clear x
  | x : BinNums.Z |- _ => clear x
  | x : unit |- _ => clear x
  | x : bool |- _ => clear x
  | x : list _ |- _ => clear x
  | x : nat |- _ => clear x
  (* same TODO as above *)
  | x := _ : Word.Interface.word.rep _ |- _ => clear x
  | x := _ : Init.Byte.byte |- _ => clear x
  | x := _ : Semantics.trace |- _ => clear x
  | x := _ : Syntax.cmd |- _ => clear x
  | x := _ : Syntax.expr |- _ => clear x
  | x := _ : coqutil.Map.Interface.map.rep |- _ => clear x
  | x := _ : BinNums.Z |- _ => clear x
  | x := _ : unit |- _ => clear x
  | x := _ : bool |- _ => clear x
  | x := _ : list _ |- _ => clear x
  | x := _ : nat |- _ => clear x
  | |- forall _, _ => intros
  | |- let _ := _ in _ => intros
  | |- dlet.dlet ?v (fun x => ?P) => change (let x := v in P); intros
  | _ => progress (cbn [Semantics.interp_binop] in * )
  | H: exists _, _ |- _ => tryif is_context_variable H then fail else destruct H
  | H: _ /\ _ |- _ => tryif is_context_variable H then fail else destruct H
  | x := ?y |- ?G => is_var y; subst x
  | H: ?x = ?y |- _ => constr_eq x y; clear H
  | H: ?x = ?y |- _ => is_var x; is_var y; assert_fails (idtac; let __ := eval cbv [x] in x in idtac); subst x
  | H: ?x = ?y |- _ => is_var x; is_var y; assert_fails (idtac; let __ := eval cbv [y] in y in idtac); subst y
  | H: ?x = ?v |- _ =>
    is_var x;
    assert_fails (idtac; let __ := eval cbv delta [x] in x in idtac);
    lazymatch v with context[x] => fail | _ => idtac end;
    let x' := fresh x in
    rename x into x';
    simple refine (let x := v in _);
    change (x' = x) in H;
    symmetry in H;
    destruct H
  end.

Import WeakestPrecondition.
Import coqutil.Map.Interface.

Ltac straightline_stackalloc :=
  match goal with Hanybytes: Memory.anybytes ?a ?n ?mStack |- _ =>
  let m := match goal with H : map.split ?mCobined ?m mStack |- _ => m end in
  let mCombined := match goal with H : map.split ?mCobined ?m mStack |- _ => mCobined end in
  let Hsplit := match goal with H : map.split ?mCobined ?m mStack |- _ => H end in
  let Hm := multimatch goal with H : _ m |- _ => H end in
  let Hm' := fresh Hm in
  let Htmp := fresh in
  let Pm := match type of Hm with ?P m => P end in
  assert_fails (assert (Separation.sep Pm (Array.array Separation.ptsto (Interface.word.of_Z (BinNums.Zpos BinNums.xH)) a _) mCombined) as _ by ecancel_assumption);
  rename Hm into Hm';
  let stack := fresh "stack" in
  let stack_length := fresh "length_" stack in (* MUST remain in context for deallocation *)
  destruct (Array.anybytes_to_array_1 mStack a n Hanybytes) as (stack&Htmp&stack_length);
  epose proof (ex_intro _ m (ex_intro _ mStack (conj Hsplit (conj Hm' Htmp)))
  : Separation.sep _ (Array.array Separation.ptsto (Interface.word.of_Z (BinNums.Zpos BinNums.xH)) a _) mCombined) as Hm;
  clear Htmp; (* note: we could clear more here if we assumed only one separation-logic description of each memory is present *)
  try (let m' := fresh m in rename m into m'); rename mCombined into m;
  ( assert (BinInt.Z.of_nat (Datatypes.length stack) = n)
  by (rewrite stack_length; apply (ZifyInst.of_nat_to_nat_eq n))
  || fail 2 "negative stackalloc of size" n )
  end.

Ltac straightline_stackdealloc :=
  lazymatch goal with |- exists _ _, Memory.anybytes ?a ?n _ /\ map.split ?m _ _ /\ _ =>
  let Hm := multimatch goal with Hm : _ m |- _ => Hm end in
  let stack := match type of Hm with context [Array.array Separation.ptsto _ a ?stack] => stack end in
  let length_stack := match goal with H : Datatypes.length stack = _ |- _ => H end in
  let Hm' := fresh Hm in
  pose proof Hm as Hm';
  let Psep := match type of Hm with ?P _ => P end in
  let Htmp := fresh "Htmp" in
  eassert (Lift1Prop.iff1 Psep (Separation.sep _ (Array.array Separation.ptsto (Interface.word.of_Z (BinNums.Zpos BinNums.xH)) a stack))) as Htmp
  by ecancel || fail "failed to find stack frame in" Psep "using ecancel";
  eapply (fun m => proj1 (Htmp m)) in Hm;
  let m' := fresh m in
  rename m into m';
  let mStack := fresh in
  destruct Hm as (m&mStack&Hsplit&Hm&Harray1); move Hm at bottom;
  pose proof Array.array_1_to_anybytes _ _ _ Harray1 as Hanybytes;
  rewrite length_stack in Hanybytes;
  refine (ex_intro _ m (ex_intro _ mStack (conj Hanybytes (conj Hsplit _))));
  clear Htmp Hsplit mStack Harray1 Hanybytes
  end.

Ltac rename_to_different H :=
  idtac;
  let G := fresh H "'0" in
  rename H into G.
Ltac ensure_free H :=
  try rename_to_different H.

Ltac eq_uniq_step :=
  match goal with
  | |- ?x = ?y =>
      let x := rdelta x in
      let y := rdelta y in
      first [ is_evar x | is_evar y | constr_eq x y ]; exact eq_refl
  | |- ?lhs = ?rhs =>
      let lh := head lhs in
      is_constructor lh;
      let rh := head rhs in
      constr_eq lh rh;
      f_equal (* NOTE: this is not sound, we really want just one f_equal application not a heuristic tactic *)
  end.
Ltac eq_uniq := repeat eq_uniq_step.

Ltac fwd_uniq_step :=
  match goal with
  | |- exists x : ?T, _ =>
      let ev := open_constr:(match _ return T with x => x end) in
      eexists ev;
      let rec f :=
        tryif has_evar ev
        then fwd_uniq_step
        else idtac
      in f
  | |- _ /\ _ => split; [ solve [repeat fwd_uniq_step; eq_uniq] | ]
  | _ => solve [ eq_uniq ]
  end.
Ltac fwd_uniq := repeat fwd_uniq_step.

Ltac straightline :=
  match goal with
  | _ => straightline_cleanup
  | |- program_logic_goal_for ?f _ =>
    enter f; intros;
    match goal with
    | H: map.get ?functions ?fname = Some _ |- _ =>
        eapply start_func; [exact H | clear H]
    end;
    cbv match beta delta [WeakestPrecondition.func]
  | |- WeakestPrecondition.cmd _ (cmd.set ?s ?e) _ _ _ ?post =>
    unfold1_cmd_goal; cbv beta match delta [cmd_body];
    let __ := match s with String.String _ _ => idtac | String.EmptyString => idtac end in
    ident_of_constr_string_cps s ltac:(fun x =>
      ensure_free x;
      (* NOTE: keep this consistent with the [exists _, _ /\ _] case far below *)
      letexists _ as x; split; [solve [repeat straightline]|])
  | |- cmd _ ?c _ _ _ ?post =>
    let c := eval hnf in c in
    lazymatch c with
    | cmd.while _ _ => fail
    | cmd.cond _ _ _ => fail
    | cmd.interact _ _ _ => fail
    | _ => unfold1_cmd_goal; cbv beta match delta [cmd_body]
    end
  | |- @list_map _ _ (get _) _ _ => unfold1_list_map_goal; cbv beta match delta [list_map_body]
  | |- @list_map _ _ (expr _ _) _ _ => unfold1_list_map_goal; cbv beta match delta [list_map_body]
  | |- @list_map _ _ _ nil _ => cbv beta match fix delta [list_map list_map_body]
  | |- expr _ _ _ _ => unfold1_expr_goal; cbv beta match delta [expr_body]
  | |- dexpr _ _ _ _ => cbv beta delta [dexpr]
  | |- dexprs _ _ _ _ => cbv beta delta [dexprs]
  | |- literal _ _ => cbv beta delta [literal]
  | |- @get ?w ?W ?L ?l ?x ?P =>
      let get' := eval cbv [get] in @get in
      change (get' w W L l x P); cbv beta
  | |- load _ _ _ _ => cbv beta delta [load]
  | |- @Loops.enforce ?width ?word ?locals ?names ?values ?map =>
    let values := eval cbv in values in
    change (@Loops.enforce width word locals names values map);
    exact (conj (eq_refl values) eq_refl)
  | |- @eq (@coqutil.Map.Interface.map.rep String.string Interface.word.rep _) _ _ =>
    eapply SortedList.eq_value; exact eq_refl
  | |- @map.get String.string Interface.word.rep ?M ?m ?k = Some ?e' =>
    let e := rdelta e' in
    is_evar e;
    once (let v := multimatch goal with x := context[@map.put _ _ M _ k ?v] |- _ => v end in
          (* cbv is slower than this, cbv with whitelist would have an enormous whitelist, cbv delta for map is slower than this, generalize unrelated then cbv is slower than this, generalize then vm_compute is slower than this, lazy is as slow as this: *)
          unify e v; exact (eq_refl (Some v)))
  | |- @coqutil.Map.Interface.map.get String.string Interface.word.rep _ _ _ = Some ?v =>
    let v' := rdelta v in is_evar v'; (change v with v'); exact eq_refl
  | |- ?x = ?y =>
    let y := rdelta y in is_evar y; change (x=y); exact eq_refl
  | |- ?x = ?y =>
    let x := rdelta x in is_evar x; change (x=y); exact eq_refl
  | |- ?x = ?y =>
    let x := rdelta x in let y := rdelta y in constr_eq x y; exact eq_refl
  | |- store Syntax.access_size.one _ _ _ _ =>
    eapply Scalars.store_one_of_sep; [solve[ecancel_assumption]|]
  | |- store Syntax.access_size.two _ _ _ _ =>
    eapply Scalars.store_two_of_sep; [solve[ecancel_assumption]|]
  | |- store Syntax.access_size.four _ _ _ _ =>
    eapply Scalars.store_four_of_sep; [solve[ecancel_assumption]|]
  | |- store Syntax.access_size.word _ _ _ _ =>
    eapply Scalars.store_word_of_sep; [solve[ecancel_assumption]|]
  | |- bedrock2.Memory.load Syntax.access_size.one ?m ?a = Some ?ev =>
    try subst ev; refine (@Scalars.load_one_of_sep _ _ _ _ _ _ _ _ _ _); ecancel_assumption
  | |- @bedrock2.Memory.load _ ?word ?mem Syntax.access_size.two ?m ?a = Some ?ev =>
    try subst ev; refine (@Scalars.load_two_of_sep _ _ word _ mem _ a _ _ m _); ecancel_assumption
  | |- @bedrock2.Memory.load _ ?word ?mem Syntax.access_size.four ?m ?a = Some ?ev =>
    try subst ev; refine (@Scalars.load_four_of_sep_32bit _ _ word _ mem _ eq_refl a _ _ m _); ecancel_assumption
  | |- @bedrock2.Memory.load _ ?word ?mem Syntax.access_size.four ?m ?a = Some ?ev =>
    try subst ev; refine (@Scalars.load_four_of_sep _ _ word _ mem _ a _ _ m _); ecancel_assumption
  | |- @bedrock2.Memory.load _ ?word ?mem Syntax.access_size.word ?m ?a = Some ?ev =>
    try subst ev; refine (@Scalars.load_word_of_sep _ _ word _ mem _ a _ _ m _); ecancel_assumption
  | |- exists l', Interface.map.of_list_zip ?ks ?vs = Some l' /\ _ =>
    letexists; split; [exact eq_refl|] (* TODO: less unification here? *)
  | |- exists l', Interface.map.putmany_of_list_zip ?ks ?vs ?l = Some l' /\ _ =>
    letexists; split; [exact eq_refl|] (* TODO: less unification here? *)
  | _ => fwd_uniq_step
  | |- exists x, ?P /\ ?Q =>
    let x := fresh x in refine (let x := _ in ex_intro (fun x => P /\ Q) x _);
                        split; [solve [repeat straightline]|]
  | |- exists x, Markers.split (?P /\ ?Q) =>
    let x := fresh x in refine (let x := _ in ex_intro (fun x => P /\ Q) x _);
                        split; [solve [repeat straightline]|]
  | |- Markers.unique (exists x, Markers.split (?P /\ ?Q)) =>
    let x := fresh x in refine (let x := _ in ex_intro (fun x => P /\ Q) x _);
                        split; [solve [repeat straightline]|]
  | |- Markers.unique (Markers.left ?G) =>
    change G;
    unshelve (idtac; repeat match goal with
                     | |- Markers.split (?P /\ Markers.right ?Q) =>
                       split; [eabstract (repeat straightline) | change Q]
                     | |- exists _, _ => letexists
                     end); []
  | |- Markers.split ?G => change G; split
  | |- True => exact I
  | |- False \/ _ => right
  | |- _ \/ False => left
  | |- BinInt.Z.modulo ?z (Memory.bytes_per_word _) = BinInt.Z0 /\ _ =>
      lazymatch Coq.setoid_ring.InitialRing.isZcst z with
      | true => split; [exact eq_refl|]
      end
  | |- _ => straightline_stackalloc
  | |- _ => straightline_stackdealloc
  | |- context[sep (sep ?_a ?_b) ?_c] => progress (flatten_seps_in_goal; cbn [seps])
  | H : context[sep (sep ?_a ?_b) ?_c] |- _ => progress (flatten_seps_in H; cbn [seps] in H)
  end.

(* TODO: once we can automatically prove some calls, include the success-only version of this in [straightline] *)
Ltac straightline_call :=
  lazymatch goal with
  | |- WeakestPrecondition.call ?functions ?callee _ _ _ _ =>
    let callee_spec := lazymatch constr:(_:spec_of callee) with ?s => s end in
    let Hcall := lazymatch goal with H: callee_spec functions |- _ => H end in
    eapply WeakestPreconditionProperties.Proper_call; cycle -1;
      [ eapply Hcall | try eabstract (solve [Morphisms.solve_proper]) .. ];
      [ .. | intros ? ? ? ?]
  end.

Ltac current_trace_mem_locals :=
  lazymatch goal with
  | |- WeakestPrecondition.cmd _  _ ?t ?m ?l _ => constr:((t, m, l))
  end.

Ltac seprewrite Hrw :=
  let tml := current_trace_mem_locals in
  let m := lazymatch tml with (_, ?m, _) => m end in
  let H := multimatch goal with H: _ m |- _ => H end in
  seprewrite_in Hrw H.
Ltac seprewrite_by Hrw tac :=
  let tml := current_trace_mem_locals in
  let m := lazymatch tml with (_, ?m, _) => m end in
  let H := multimatch goal with H: _ m |- _ => H end in
  seprewrite_in_by Hrw H tac.

Ltac show_program :=
  lazymatch goal with
  | |- @cmd ?width ?BW ?word ?mem ?locals ?ext_spec ?E ?c ?F ?G ?H ?I =>
    let c' := eval cbv in c in
    change (@cmd width BW word mem locals ext_spec E (fst (c, c')) F G H I)
  end.

Ltac subst_words :=
  repeat match goal with x := _ : coqutil.Word.Interface.word.rep |- _ => subst x end.

Require Import coqutil.Tactics.eplace Coq.setoid_ring.Ring_tac.
Ltac ring_simplify_words :=
  subst_words;
  repeat match goal with H : context [?w] |- _ =>
    let __ := constr:(w : Interface.word.rep) in
    progress eplace w with _ in H by (ring_simplify; reflexivity) end;
  repeat match goal with |- context [?w] =>
    let __ := constr:(w : Interface.word.rep) in
    progress eplace w with _ by (ring_simplify; reflexivity) end.
