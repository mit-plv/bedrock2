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

Ltac straightline_cleanup_clear :=
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
  end.
Ltac cbn_interp_binop :=
  progress (cbn [Semantics.interp_binop] in * ).
Ltac straightline_cleanup_intros :=
  idtac;
  match goal with
  | |- forall _, _ => intros
  | |- let _ := _ in _ => intros
  | |- dlet.dlet ?v (fun x => ?P) => change (let x := v in P); intros
  end.
Ltac straightline_cleanup_destruct :=
  idtac;
  match goal with
  | H: exists _, _ |- _ => destruct H
  | H: _ /\ _ |- _ => destruct H
  end.
Ltac straightline_cleanup_subst_constr_eq x y H :=
  constr_eq x y; clear H.
Ltac assert_not_unfoldable x :=
  assert_fails (idtac; let __ := eval cbv [x] in x in idtac).
Ltac straightline_cleanup_subst_let x y H :=
  lazymatch y with context[x] => fail | _ => idtac end;
  let x' := fresh x in
  rename x into x';
  simple refine (let x := y in _);
  change (x' = x) in H;
  symmetry in H;
  destruct H.
Ltac straightline_cleanup_subst :=
  idtac;
  match goal with
  | x := ?y |- ?G => is_var y; subst x
  | H: ?x = ?y |- _
    => first [ straightline_cleanup_subst_constr_eq x y H
             | is_var x;
       first [ assert_not_unfoldable x;
       first [ is_var y;
       first [ subst x
             | assert_not_unfoldable y; subst y ]
             | straightline_cleanup_subst_let x y H ]
             | is_var y;
               assert_not_unfoldable y; subst y ] ]
  end.

Ltac straightline_cleanup :=
  first [ straightline_cleanup_clear
        | straightline_cleanup_intros
        | cbn_interp_binop
        | straightline_cleanup_destruct
        | straightline_cleanup_subst ].

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

Ltac ensure_free H :=
  let G := fresh H in
  try rename H into G.

Ltac straightline :=
  first [ straightline_cleanup
        | let f := match goal with |- program_logic_goal_for ?f _ => f end in
    enter f; intros;
    unfold1_call_goal; cbv match beta delta [call_body];
    lazymatch goal with |- if ?test then ?T else _ =>
      replace test with true by reflexivity; change T end;
    cbv match beta delta [WeakestPrecondition.func]
        | let s := match goal with |- WeakestPrecondition.cmd _ (cmd.set ?s ?e) _ _ _ ?post => s end in
          let e := match goal with |- WeakestPrecondition.cmd _ (cmd.set ?s ?e) _ _ _ ?post => e end in
          let post := match goal with |- WeakestPrecondition.cmd _ (cmd.set ?s ?e) _ _ _ ?post => post end in
    unfold1_cmd_goal; cbv beta match delta [cmd_body];
    let x := ident_of_string s in
    ensure_free x;
    (* NOTE: keep this consistent with the [exists _, _ /\ _] case far below *)
    letexists _ as x; split; [solve [repeat straightline]|]
                | let c := match goal with |- cmd _ ?c _ _ _ ?post => c end in
                  let post := match goal with |- cmd _ ?c _ _ _ ?post => post end in
    let c := eval hnf in c in
    lazymatch c with
    | cmd.while _ _ => fail
    | cmd.cond _ _ _ => fail
    | cmd.interact _ _ _ => fail
    | _ => idtac
    end; unfold1_cmd_goal; cbv beta match delta [cmd_body]
  | match goal with |- @list_map _ _ (get _) _ _ => idtac end; unfold1_list_map_goal; cbv beta match delta [list_map_body]
  | match goal with |- @list_map _ _ (expr _ _) _ _ => idtac end; unfold1_list_map_goal; cbv beta match delta [list_map_body]
  | match goal with |- @list_map _ _ _ nil _ => idtac end; cbv beta match fix delta [list_map list_map_body]
  | match goal with |- expr _ _ _ _ => idtac end; unfold1_expr_goal; cbv beta match delta [expr_body]
  | match goal with |- dexpr _ _ _ _ => idtac end; cbv beta delta [dexpr]
  | match goal with |- dexprs _ _ _ _ => idtac end; cbv beta delta [dexprs]
  | match goal with |- literal _ _ => idtac end; cbv beta delta [literal]
  | match goal with |- get _ _ _ => idtac end; cbv beta delta [get]
  | match goal with |- load _ _ _ _ => idtac end; cbv beta delta [load]
  | match goal with |- @Loops.enforce ?width ?word ?locals ?names ?values ?map =>
    let values := eval cbv in values in
    change (@Loops.enforce width word locals names values map);
    exact (conj (eq_refl values) eq_refl) end
  | match goal with |- @eq (@coqutil.Map.Interface.map.rep String.string Interface.word.rep _) _ _ => idtac end;
    eapply SortedList.eq_value; exact eq_refl
  | match goal with |- @map.get String.string Interface.word.rep ?M ?m ?k = Some ?e' =>
    let e := rdelta e' in
    is_evar e;
    once (let v := multimatch goal with x := context[@map.put _ _ M _ k ?v] |- _ => v end in
          (* cbv is slower than this, cbv with whitelist would have an enormous whitelist, cbv delta for map is slower than this, generalize unrelated then cbv is slower than this, generalize then vm_compute is slower than this, lazy is as slow as this: *)
          unify e v; exact (eq_refl (Some v))) end
  | let v := match goal with |- @coqutil.Map.Interface.map.get String.string Interface.word.rep _ _ _ = Some ?v => v end in
    let v' := rdelta v in is_evar v'; (change v with v'); exact eq_refl
  | let x := match goal with |- ?x = ?y => x end in
    let y := match goal with |- ?x = ?y => y end in
    first [ let y := rdelta y in is_evar y; change (x=y); exact eq_refl
          | let x := rdelta x in is_evar x; change (x=y); exact eq_refl
          | let x := rdelta x in let y := rdelta y in constr_eq x y; exact eq_refl ]
  | match goal with |- store Syntax.access_size.one _ _ _ _ => idtac end;
    eapply Scalars.store_one_of_sep; [solve[ecancel_assumption]|]
  | match goal with |- store Syntax.access_size.two _ _ _ _ => idtac end;
    eapply Scalars.store_two_of_sep; [solve[ecancel_assumption]|]
  | match goal with |- store Syntax.access_size.four _ _ _ _ => idtac end;
    eapply Scalars.store_four_of_sep; [solve[ecancel_assumption]|]
  | match goal with |- store Syntax.access_size.word _ _ _ _ => idtac end;
    eapply Scalars.store_word_of_sep; [solve[ecancel_assumption]|]
  | let ev := match goal with |- bedrock2.Memory.load Syntax.access_size.one ?m ?a = Some ?ev => ev end in
    try subst ev; refine (@Scalars.load_one_of_sep _ _ _ _ _ _ _ _ _ _); ecancel_assumption
  | match goal with |- @bedrock2.Memory.load _ ?word ?mem Syntax.access_size.two ?m ?a = Some ?ev =>
    try subst ev; refine (@Scalars.load_two_of_sep _ word _ mem _ a _ _ m _); ecancel_assumption end
  | match goal with |- @bedrock2.Memory.load _ ?word ?mem Syntax.access_size.four ?m ?a = Some ?ev =>
    try subst ev; refine (@Scalars.load_four_of_sep_32bit _ word _ mem _ eq_refl a _ _ m _); ecancel_assumption end
  | match goal with |- @bedrock2.Memory.load _ ?word ?mem Syntax.access_size.four ?m ?a = Some ?ev =>
    try subst ev; refine (@Scalars.load_four_of_sep _ word _ mem _ a _ _ m _); ecancel_assumption end
  | match goal with |- @bedrock2.Memory.load _ ?word ?mem Syntax.access_size.word ?m ?a = Some ?ev =>
    try subst ev; refine (@Scalars.load_word_of_sep _ word _ mem _ a _ _ m _); ecancel_assumption end
  | match goal with |- exists l', Interface.map.of_list_zip ?ks ?vs = Some l' /\ _ => idtac end;
    letexists; split; [exact eq_refl|] (* TODO: less unification here? *)
  | match goal with |- exists l', Interface.map.putmany_of_list_zip ?ks ?vs ?l = Some l' /\ _ => idtac end;
    letexists; split; [exact eq_refl|] (* TODO: less unification here? *)
  | match goal with |- exists x, ?P /\ ?Q =>
    let x := fresh x in refine (let x := _ in ex_intro (fun x => P /\ Q) x _);
                        split; [solve [repeat straightline]|]
  | |- exists x, Markers.split (?P /\ ?Q) =>
    let x := fresh x in refine (let x := _ in ex_intro (fun x => P /\ Q) x _);
                        split; [solve [repeat straightline]|]
  | |- Markers.unique (exists x, Markers.split (?P /\ ?Q)) =>
    let x := fresh x in refine (let x := _ in ex_intro (fun x => P /\ Q) x _);
                        split; [solve [repeat straightline]|] end
  | let G := match goal with |- Markers.unique (Markers.left ?G) => G end in
    change G;
    unshelve (idtac; repeat match goal with
                     | |- Markers.split (?P /\ Markers.right ?Q) =>
                       split; [eabstract (repeat straightline) | change Q]
                     | |- exists _, _ => letexists
                     end); []
  | let G := match goal with |- Markers.split ?G => G end in
    change G; split
  | match goal with |- True => idtac end; exact I
  | match goal with |- False \/ _ => idtac end; right
  | match goal with |- _ \/ False => idtac end; left
  | let z := match goal with |- BinInt.Z.modulo ?z (Memory.bytes_per_word _) = BinInt.Z0 /\ _ => z end in
      lazymatch Coq.setoid_ring.InitialRing.isZcst z with
      | true => idtac
      end;
      split; [exact eq_refl|]
  | straightline_stackalloc
  | straightline_stackdealloc ].

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
