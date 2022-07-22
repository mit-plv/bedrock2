Require Import coqutil.Macros.subst coqutil.Macros.unique bedrock2.Syntax.
From coqutil.Tactics Require Import letexists eabstract rdelta ident_of_string.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.Loops.
Require Import bedrock2.Map.SeparationLogic bedrock2.Scalars.

Definition spec_of (procname:String.string) := list (String.string * (list String.string * list String.string * Syntax.cmd.cmd)) -> Prop.
Existing Class spec_of.

Module Import Coercions.
  Import Map.Interface Word.Interface BinInt.
  Coercion Z.of_nat : nat >-> Z.
  Coercion word.unsigned : word.rep >-> Z.

  Definition sepclause_of_map {key value map} (m : @map.rep key value map)
    : map.rep -> Prop := Logic.eq m.
  Coercion sepclause_of_map : Interface.map.rep >-> Funclass.
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

(* TODO: use a deduplicating set instead of a list *)
Fixpoint callees (c : Syntax.cmd) : list String.string :=
  match c with
  | cmd.cond _ c1 c2 | cmd.seq c1 c2 => callees c1 ++ callees c2
  | cmd.while _ c | cmd.stackalloc _ _ c => callees c
  | cmd.call _ f _ => cons f nil
  | _ => nil
  end.

Ltac assuming_correctness_of_in callees functions P :=
  lazymatch callees with
  | nil => P
  | cons ?f ?callees =>
    let f_spec := lazymatch constr:(_:spec_of f) with ?x => x end in
    constr:(f_spec functions -> ltac:(let t := assuming_correctness_of_in callees functions P in exact t))
  end.
Local Notation function_t := ((String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type).
Local Notation functions_t := (list function_t).

Ltac program_logic_goal_for_function proc :=
  let __ := constr:(proc : function_t) in
  let fname := eval cbv in (fst proc) in
  let callees := eval cbv in (callees (snd (snd proc))) in
  let spec := lazymatch constr:(_:spec_of fname) with ?s => s end in
  constr:(forall functions : functions_t, ltac:(
    let s := assuming_correctness_of_in callees functions (spec (cons proc functions)) in
    exact s)).
Definition program_logic_goal_for (_ : function_t) (P : Prop) := P.

Notation "program_logic_goal_for_function! proc" := (program_logic_goal_for proc ltac:(
   let x := program_logic_goal_for_function proc in exact x))
  (at level 10, only parsing).

(* Users might want to override this with
     Ltac normalize_body_of_function f ::= Tactics.rdelta.rdelta f.
   in case cbv does more simplification than desired. *)
Ltac normalize_body_of_function f := eval cbv in f.

Ltac bind_body_of_function f_ :=
  let f := normalize_body_of_function f_ in
  let fname := open_constr:(_) in
  let fargs := open_constr:(_) in
  let frets := open_constr:(_) in
  let fbody := open_constr:(_) in
  let funif := open_constr:((fname, (fargs, frets, fbody))) in
  unify f funif;
  let G := lazymatch goal with |- ?G => G end in
  let P := lazymatch eval pattern f_ in G with ?P _ => P end in
  change (bindcmd fbody (fun c : Syntax.cmd => P (fname, (fargs, frets, c))));
  cbv beta iota delta [bindcmd]; intros.

Ltac app_head e :=
  match e with
  | ?f ?a => app_head f
  | _ => e
  end.

(* note: f might have some implicit parameters (eg a record of constants) *)
Ltac enter f :=
  cbv beta delta [program_logic_goal_for]; intros;
  bind_body_of_function f;
  lazymatch goal with |- ?s _ => cbv beta delta [s] end.

Require coqutil.Map.SortedList. (* special-case eq_refl *)

From Ltac2 Require Notations Control.
Module Ltac2ForPerf.
  Import Ltac2.Notations Ltac2.Init.
  Ltac2 straightline_cleanup_clear () :=
    let h := Control.hyps () in
    let should_clear_type ty := (match! ty with
  (* TODO remove superfluous _ after .rep, but that will break some proofs that rely on
     x not being cleared to instantiate evars with terms depending on x *)
  | Word.Interface.word.rep _ => true
  | Init.Byte.byte => true
  | Semantics.trace => true
  | Syntax.cmd => true
  | Syntax.expr => true
  | coqutil.Map.Interface.map.rep => true
  | BinNums.Z => true
  | unit => true
  | bool => true
  | list _ => true
  | nat => true
  | _ => false
                                 end) in
    let h := List.filter (fun (name, body, ty) => should_clear_type ty) h in
    progress (List.iter (fun (name, _, _) => try (clear $name)) h).
End Ltac2ForPerf.

(* Use [first] rather than [match] so we see a more accurate Ltac profile *)
Ltac straightline_cleanup :=
  first [ ltac2:(Ltac2ForPerf.straightline_cleanup_clear ())
        | match goal with
          | |- forall _, _ => idtac
          | |- let _ := _ in _ => idtac
          end;
          intros
        | match goal with
          | |- dlet.dlet ?v (fun x => ?P) => change (let x := v in P)
          end; intros
        | progress (cbn [Semantics.interp_binop] in * )
        | let H := match goal with
                   | H: exists _, _ |- _ => H
                   | H: _ /\ _ |- _ => H
                   end in
          destruct H
        | match goal with
          | x := ?y |- ?G => is_var y; subst x
          end
        | let H := multimatch goal with | H: ?x = ?v |- _ => H end in
          let x := lazymatch type of H with ?x = ?y => x end in
          let y := lazymatch type of H with ?x = ?y => y end in
          first [ constr_eq x y; clear H
                | is_var x; is_var y; assert_fails (idtac; let __ := eval cbv [x] in x in idtac); subst x
                | is_var x; is_var y; assert_fails (idtac; let __ := eval cbv [y] in y in idtac); subst y
                | is_var x;
                  assert_fails (idtac; let __ := eval cbv delta [x] in x in idtac);
                  lazymatch y with context[x] => fail | _ => idtac end;
                  let x' := fresh x in
                  rename x into x';
                  simple refine (let x := y in _);
                  change (x' = x) in H;
                  symmetry in H;
                  destruct H ] ].

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
  assert_fails (idtac; match goal with Halready : (Separation.sep Pm (Array.array Separation.ptsto (Interface.word.of_Z (BinNums.Zpos BinNums.xH)) a _) mCombined) |- _ => idtac end);
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

Ltac rename_to_different H := once (idtac;
  let G := fresh H in
  rename H into G;
  assert_succeeds (set (H := Set))).
Ltac ensure_free H :=
  match constr:(Set) with
  | _ => assert_succeeds (set (H := Set))
  | _ => rename_to_different H
  end.

Ltac straightline :=
  match goal with
  | _ => straightline_cleanup
  | |- program_logic_goal_for ?f _ =>
    enter f; intros;
    unfold1_call_goal; cbv match beta delta [call_body];
    lazymatch goal with |- if ?test then ?T else _ =>
      replace test with true by reflexivity; change T end;
    cbv match beta delta [WeakestPrecondition.func]
  | |- WeakestPrecondition.cmd _ (cmd.set ?s ?e) _ _ _ ?post =>
    unfold1_cmd_goal; cbv beta match delta [cmd_body];
    let x := ident_of_string s in
    ensure_free x;
    (* NOTE: keep this consistent with the [exists _, _ /\ _] case far below *)
    letexists _ as x; split; [solve [repeat straightline]|]
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
  | |- get _ _ _ => cbv beta delta [get]
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

Module ProofPrintingNotations.
  Notation "'need!' y 's.t.' Px 'let' x ':=' v 'using' pfPx 'in' pfP" :=
    (let x := v in ex_intro (fun y => Px /\ _) x (conj pfPx pfP))
    (right associativity, at level 200, pfPx at next level,
      format "'need!'  y  's.t.'  Px  '/' 'let'  x  ':='  v  'using'  pfPx  'in'  '/' pfP").
  Notation "'need!' x 's.t.' Px 'let' x ':=' v 'using' pfPx 'in' pfP" :=
    (let x := v in ex_intro (fun x => Px /\ _) x (conj pfPx pfP))
    (only printing, right associativity, at level 200, pfPx at next level,
      format "'need!'  x  's.t.'  Px  '/' 'let'  x  ':='  v  'using'  pfPx  'in'  '/' pfP").
  Notation "'need!' y 's.t.' Px 'let' x ':=' v 'using' pfPx 'in' pfP" :=
    (let x := v in ex_intro (fun y => Px /\ _) x (conj pfPx pfP))
    (right associativity, at level 200, pfPx at next level,
     format "'need!'  y  's.t.'  Px  '/' 'let'  x  ':='  v  'using'  pfPx  'in'  '/' pfP")
    : type_scope.
  Notation "'need!' x 's.t.' Px 'let' x ':=' v 'using' pfPx 'in' pfP" :=
    (let x := v in ex_intro (fun x => Px /\ _) x (conj pfPx pfP))
    (only printing, right associativity, at level 200, pfPx at next level,
     format "'need!'  x  's.t.'  Px  '/' 'let'  x  ':='  v  'using'  pfPx  'in'  '/' pfP")
    : type_scope.
End ProofPrintingNotations.
