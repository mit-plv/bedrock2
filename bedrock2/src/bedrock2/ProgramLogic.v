From coqutil.Tactics Require Import Tactics letexists eabstract rdelta reference_to_string ident_of_string.
Require Import coqutil.Map.Interface.
Require coqutil.Datatypes.ListSet.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.Loops.
Require Import coqutil.Map.Separation coqutil.Map.SeparationLogic bedrock2.Scalars.
Require Import coqutil.Map.OfListWord.

Definition spec_of (procname:String.string) := Semantics.env -> Prop.
Existing Class spec_of.

Module Import Coercions.
  Export Separation.Coercions.
  Notation sepclause_of_map := Separation.exact (only parsing).
  Import Word.Interface BinInt.
  Coercion Z.of_nat : nat >-> Z.
  Coercion word.unsigned : word.rep >-> Z.
End Coercions.

Goal True.
  assert_succeeds epose (fun k v M (m : @Interface.map.rep k v M) => m _).
Abort.

Section bindcmd.
  Context {T : Type}.
  Fixpoint bindcmd (c : Syntax.cmd) (k : Syntax.cmd -> T) {struct c} : T :=
    match c with
    | cmd.cond e c1 c2 => bindcmd c1 (fun c1 => bindcmd c2 (fun c2 => let c := cmd.cond e c1 c2 in k c))
    | cmd.seq c1 c2 => bindcmd c1 (fun c1 => bindcmd c2 (fun c2 => let c := cmd.seq c1 c2 in k c))
    | cmd.while e c => bindcmd c (fun c => let c := cmd.while e c in k c)
    | c => k c
    end.
End bindcmd.

(* TODO replace callees by callees' to avoid duplicates *)

Fixpoint callees (c : Syntax.cmd) : list String.string :=
  match c with
  | cmd.cond _ c1 c2 | cmd.seq c1 c2 => callees c1 ++ callees c2
  | cmd.while _ c | cmd.stackalloc _ _ c => callees c
  | cmd.call _ f _ => cons f nil
  | _ => nil
  end.

Fixpoint callees' (c : Syntax.cmd) : list String.string :=
  match c with
  | cmd.cond _ c1 c2 | cmd.seq c1 c2 => ListSet.list_union String.eqb (callees c1) (callees c2)
  | cmd.while _ c | cmd.stackalloc _ _ c => callees' c
  | cmd.call _ f _ => cons f nil
  | _ => nil
  end.

(* returns a list of (caller, list_of_direct_callees) tuples *)
Definition callgraph: list (String.string * Syntax.func) ->
                      list (String.string * list String.string) :=
  List.map (fun '(fname, (_, _, fbody)) => (fname, callees' fbody)).

Ltac assuming_correctness_of_in callees functions P :=
  lazymatch callees with
  | nil => P
  | cons ?f ?callees =>
    let f_spec := lazymatch constr:(_:spec_of f) with ?x => x end in
    constr:(f_spec functions -> ltac:(let t := assuming_correctness_of_in callees functions P in exact t))
  end.
Require Import String List coqutil.Macros.ident_to_string.

Ltac program_logic_goal_for_function proc :=
  let __ := constr:(proc : Syntax.func) in
  constr_string_basename_of_constr_reference_cps ltac:(Tactics.head proc) ltac:(fun fname =>
  let spec := lazymatch constr:(_:spec_of fname) with ?s => s end in
  exact (forall (functions : @map.rep _ _ Semantics.env) (EnvContains : map.get functions fname = Some proc), ltac:(
    let callees := eval cbv in (callees (snd proc)) in
    let s := assuming_correctness_of_in callees functions (spec functions) in
    exact s))).
Definition program_logic_goal_for (_ : Syntax.func) (P : Prop) := P.

Notation "program_logic_goal_for_function! proc" := (program_logic_goal_for proc ltac:(
   program_logic_goal_for_function proc))
  (at level 10, only parsing).

(* Users might want to override this with
     Ltac normalize_body_of_function f ::= Tactics.rdelta.rdelta f.
   in case cbv does more simplification than desired. *)
Ltac normalize_body_of_function f := eval cbv in f.

Ltac bind_body_of_function f_ :=
  let f := normalize_body_of_function f_ in
  let fargs := open_constr:(_) in
  let frets := open_constr:(_) in
  let fbody := open_constr:(_) in
  let funif := open_constr:((fargs, frets, fbody)) in
  unify f funif;
  let G := lazymatch goal with |- ?G => G end in
  let P := lazymatch eval pattern f_ in G with ?P _ => P end in
  change (bindcmd fbody (fun c : Syntax.cmd => P (fargs, frets, c)));
  cbv beta iota delta [bindcmd]; intros.

(* note: f might have some implicit parameters (eg a record of constants) *)
Ltac enter f :=
  cbv beta delta [program_logic_goal_for];
  bind_body_of_function f;
  lazymatch goal with |- ?s ?p => let s := rdelta s in change (s p); cbv beta end.

Require coqutil.Map.SortedList. (* special-case eq_refl *)

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
  | H: exists _, _ |- _ => assert_succeeds progress destruct H as (_&_); destruct H
  | H: _ /\ _ |- _ => destruct H
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
  match goal with Hsplit : map.split ?M ?m (OfListWord.map.of_list_word_at ?a ?stack) |- _ =>
    repeat match goal with Hm : _ m |- _ =>
      let Hm' := fresh Hm in rename Hm into Hm';
        unique pose proof ((ex_intro _ m (ex_intro _ _ (conj Hsplit (conj Hm' eq_refl))))
      : sep _ (Separation.exact (OfListWord.map.of_list_word_at a stack)) M) as Hm
    end;
    change (id (map.split M m (OfListWord.map.of_list_word_at a stack))) in Hsplit
  end.

Ltac straightline_stackdealloc :=
  lazymatch goal with |- exists _ _, map.split ?m _ (_$@?a) /\ BinIntDef.Z.of_nat (length _) = ?n /\ _ =>
    match goal with Hm : _ m |- _ =>
    let stack := match type of Hm with context [?stack$@a] => stack end in
    let length_stack := match goal with H : BinIntDef.Z.of_nat (Datatypes.length stack) = _ |- _ => H end in
    let Pm := match type of Hm with ?P _ => P end in
    let Hm' := fresh Hm in eassert (Lift1Prop.impl1 Pm (sep _ (_$@a))) as Hm'
      by ecancel || fail "failed to find stack frame in" Pm "using ecancel";
    specialize (Hm' m Hm);
    let m' := fresh m in rename m into m';
    let Hsplit := fresh in case Hm' as (m&?&Hsplit&Hm'&<-); move Hm' at bottom;
    refine (ex_intro _ m (ex_intro _ stack (conj Hsplit (conj length_stack  _)))); clear Hsplit
  end end.

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
  | |- _ => straightline_stackalloc
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
    try subst ev; refine (@Scalars.load_two_of_sep _ word _ mem _ a _ _ m _); ecancel_assumption
  | |- @bedrock2.Memory.load _ ?word ?mem Syntax.access_size.four ?m ?a = Some ?ev =>
    try subst ev; refine (@Scalars.load_four_of_sep_32bit _ word _ mem _ eq_refl a _ _ m _); ecancel_assumption
  | |- @bedrock2.Memory.load _ ?word ?mem Syntax.access_size.four ?m ?a = Some ?ev =>
    try subst ev; refine (@Scalars.load_four_of_sep _ word _ mem _ a _ _ m _); ecancel_assumption
  | |- @bedrock2.Memory.load _ ?word ?mem Syntax.access_size.word ?m ?a = Some ?ev =>
    try subst ev; refine (@Scalars.load_word_of_sep _ word _ mem _ a _ _ m _); ecancel_assumption
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
  | |- _ => straightline_stackdealloc
  | |- context[sep (sep _ _) _] => progress (flatten_seps_in_goal; cbn [seps])
  | H : context[sep (sep _ _) _] |- _ => progress (flatten_seps_in H; cbn [seps] in H)
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
