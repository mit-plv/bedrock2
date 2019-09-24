Require Import coqutil.Macros.subst coqutil.Macros.unique bedrock2.Syntax.
From coqutil.Tactics Require Import letexists eabstract rdelta.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.TailRecursion.
Require Import bedrock2.Map.SeparationLogic bedrock2.Scalars.
Require bedrock2.string2ident.

Definition spec_of {p:parameters} (procname:Syntax.funname) := list (Syntax.funname * (list Syntax.varname * list Syntax.varname * Syntax.cmd.cmd)) -> Prop.
Existing Class spec_of.

Section bindcmd.
  Context {p : Syntax.parameters} {T : Type}.
  Fixpoint bindcmd (c : Syntax.cmd) (k : Syntax.cmd -> T) {struct c} : T :=
    match c with
    | cmd.cond e c1 c2 => bindcmd c1 (fun c1 => bindcmd c2 (fun c2 => let c := cmd.cond e c1 c2 in k c))
    | cmd.seq c1 c2 => bindcmd c1 (fun c1 => bindcmd c2 (fun c2 => let c := cmd.seq c1 c2 in k c))
    | cmd.while e c => bindcmd c (fun c => let c := cmd.while e c in k c)
    | c => k c
    end.
End bindcmd.

Section callees.
  Context {p : Syntax.parameters}.
  (* TODO: use a deduplicating set instead of a list *)
  Fixpoint callees (c : Syntax.cmd) : list funname :=
    match c with
    | cmd.cond _ c1 c2 | cmd.seq c1 c2 => callees c1 ++ callees c2
    | cmd.while _ c => callees c
    | cmd.call _ f _ => cons f nil
    | _ => nil
    end.
End callees.

Ltac assuming_correctness_of_in callees functions P :=
  lazymatch callees with
  | nil => P
  | cons ?f ?callees =>
    let f_spec := lazymatch constr:(_:spec_of f) with ?x => x end in
    constr:(f_spec functions -> ltac:(let t := assuming_correctness_of_in callees functions P in exact t))
  end.
Local Notation function_t := ((funname * (list varname * list varname * Syntax.cmd.cmd))%type).
Local Notation functions_t := (list function_t).

Ltac program_logic_goal_for_function proc :=
  let __ := constr:(proc : function_t) in
  let fname := eval cbv in (fst proc) in
  let callees := eval cbv in (callees (snd (snd proc))) in
  let spec := lazymatch constr:(_:spec_of fname) with ?s => s end in
  constr:(forall functions : functions_t, ltac:(
    let s := assuming_correctness_of_in callees functions (spec (cons proc functions)) in
    exact s)).
Definition program_logic_goal_for {_:parameters} (_ : function_t) (P : Prop) := P.

Notation "program_logic_goal_for_function! proc" := (program_logic_goal_for proc ltac:(
   let x := program_logic_goal_for_function proc in exact x))
  (at level 10, only parsing).

Ltac bind_body_of_function f_ :=
  let f := eval cbv in f_ in
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

Ltac enter f :=
  cbv beta delta [program_logic_goal_for]; intros;
  bind_body_of_function f;
  let fdefn := eval cbv delta [f] in f in
  let ctx := string2ident.learn fdefn in
  let H := fresh "_string_to_ident" in
  pose ctx as H;
  lazymatch goal with |- ?s _ => cbv beta delta [s] end.

Require coqutil.Map.SortedList. (* special-case eq_refl *)

Ltac straightline_cleanup :=
  match goal with
  | x : Word.Interface.word.rep _ |- _ => clear x
  | x : Semantics.word |- _ => clear x
  | x : Semantics.byte |- _ => clear x
  | x : Semantics.locals |- _ => clear x
  | x : Semantics.trace |- _ => clear x
  | x : Syntax.cmd |- _ => clear x
  | x : Syntax.expr |- _ => clear x
  | x : coqutil.Map.Interface.map.rep |- _ => clear x
  | x : BinNums.Z |- _ => clear x
  | x : unit |- _ => clear x
  | x : bool |- _ => clear x
  | x : list _ |- _ => clear x
  | x : nat |- _ => clear x
  | x := _ : Word.Interface.word.rep _ |- _ => clear x
  | x := _ : Semantics.word |- _ => clear x
  | x := _ : Semantics.byte |- _ => clear x
  | x := _ : Semantics.locals |- _ => clear x
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
  | H: exists _, _ |- _ => destruct H
  | H: _ /\ _ |- _ => destruct H
  | x := ?y |- ?G => is_var y; subst x
  | H: ?x = ?y |- _ => constr_eq x y; clear H
  | H: ?x = ?y |- _ => is_var x; is_var y; assert_fails (idtac; let __ := eval cbv [x] in x in idtac); subst x
  | H: ?x = ?y |- _ => is_var x; is_var y; assert_fails (idtac; let __ := eval cbv [y] in y in idtac); subst y
  | H: ?x = ?v |- _ =>
    is_var x;
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

Ltac straightline :=
  match goal with
  | _ => straightline_cleanup
  | |- program_logic_goal_for ?f _ =>
    enter f; intros;
    unfold1_call_goal; cbv match beta delta [call_body];
    lazymatch goal with |- if ?test then ?T else _ =>
      replace test with true by reflexivity; change T end;
    cbv match beta delta [WeakestPrecondition.func]
  | names := _ : string2ident.Context.list
             |- @WeakestPrecondition.cmd _ _ (cmd.set ?s ?e) _ _ _ ?post =>
    unfold1_cmd_goal; cbv beta match delta [cmd_body];
    let names := eval cbv [names] in names in
    let x := string2ident.lookup s names in
    string2ident.ensure_free x;
    (* NOTE: keep this consistent with the [exists _, _ /\ _] case far below *)
    letexists _ as x; split; [solve [repeat straightline]|]
  | |- @cmd _ _ ?c _ _ _ ?post =>
    let c := eval hnf in c in
    lazymatch c with
    | cmd.while _ _ => fail
    | cmd.cond _ _ _ => fail
    | cmd.interact _ _ _ => fail
    | _ => unfold1_cmd_goal; cbv beta match delta [cmd_body]
    end
  | |- @list_map _ _ (@get _ _) _ _ => unfold1_list_map_goal; cbv beta match delta [list_map_body]
  | |- @list_map _ _ (@expr _ _ _) _ _ => unfold1_list_map_goal; cbv beta match delta [list_map_body]
  | |- @list_map _ _ _ nil _ => cbv beta match fix delta [list_map list_map_body]
  | |- @expr _ _ _ _ _ => unfold1_expr_goal; cbv beta match delta [expr_body]
  | |- @dexpr _ _ _ _ _ => cbv beta delta [dexpr]
  | |- @dexprs _ _ _ _ _ => cbv beta delta [dexprs]
  | |- @literal _ _ _ => cbv beta delta [literal]
  | |- @get _ _ _ _ => cbv beta delta [get]
  | |- @load _ _ _ _ _ => cbv beta delta [load]
  | |- TailRecursion.enforce ?names ?values ?map =>
    let values := eval cbv in values in
    change (TailRecursion.enforce names values map);
    exact (conj (eq_refl values) eq_refl)
  | |- @eq (@coqutil.Map.Interface.map.rep _ _ (@Semantics.locals _)) _ _ =>
    eapply SortedList.eq_value; exact eq_refl
  | |- map.get _ _ = Some ?e' =>
    let e := rdelta e' in
    is_evar e;
    let M := lazymatch goal with |- @map.get _ _ ?M _ _ = _ => M end in
    let __ := match M with @Semantics.locals _ => idtac end in
    let k := lazymatch goal with |- map.get _ ?k = _ => k end in
    once (let v := multimatch goal with x := context[@map.put _ _ M _ k ?v] |- _ => v end in
          (* cbv is slower than this, cbv with whitelist would have an enormous whitelist, cbv delta for map is slower than this, generalize unrelated then cbv is slower than this, generalize then vm_compute is slower than this, lazy is as slow as this: *)
          unify e v; exact (eq_refl (Some v)))
  | |- @coqutil.Map.Interface.map.get _ _ (@Semantics.locals _) _ _ = Some ?v =>
    let v' := rdelta v in is_evar v'; (change v with v'); exact eq_refl
  | |- ?x = ?y =>
    let y := rdelta y in is_evar y; change (x=y); exact eq_refl
  | |- ?x = ?y =>
    let x := rdelta x in is_evar x; change (x=y); exact eq_refl
  | |- ?x = ?y =>
    let x := rdelta x in let y := rdelta y in constr_eq x y; exact eq_refl
  | |- @store _ Syntax.access_size.one _ _ _ _ =>  eapply Scalars.store_one_of_sep; [solve[ecancel_assumption]|]
  | |- @store _ Syntax.access_size.two _ _ _ _ =>  eapply Scalars.store_two_of_sep; [solve[ecancel_assumption]|]
  | |- @store _ Syntax.access_size.four _ _ _ _ =>  eapply Scalars.store_four_of_sep; [solve[ecancel_assumption]|]
  | |- @store _ Syntax.access_size.word _ _ _ _ =>  eapply Scalars.store_word_of_sep; [solve[ecancel_assumption]|]
  | |- bedrock2.Memory.load Syntax.access_size.one ?m ?a = Some ?ev =>
    try subst ev; refine (@Scalars.load_one_of_sep _ _ _ _ _ _ _ _ _ _); ecancel_assumption
  | |- @bedrock2.Memory.load ?byte _ ?word ?mem Syntax.access_size.two ?m ?a = Some ?ev =>
    try subst ev; refine (@Scalars.load_two_of_sep _ word byte _ _ _ mem _ _ _ _ _ _); ecancel_assumption
  | |- @bedrock2.Memory.load ?byte _ ?word ?mem Syntax.access_size.four ?m ?a = Some ?ev =>
    try subst ev; refine (@Scalars.load_four_of_sep _ word byte _ _ _ mem _ _ _ _ _ _); ecancel_assumption
  | |- bedrock2.Memory.load Syntax.access_size.word ?m ?a = Some ?ev =>
    try subst ev; refine (@Scalars.load_word_of_sep _ _ _ _ _ _ _ _ _ _ _ _); ecancel_assumption
  | |- exists l', Interface.map.of_list ?ks ?vs = Some l' /\ _ =>
    letexists; split; [exact eq_refl|] (* TODO: less unification here? *)
  | |- exists l', Interface.map.putmany_of_list ?ks ?vs ?l = Some l' /\ _ =>
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
  | |- Markers.unique (Markers.left _) =>
    unshelve (idtac; repeat match goal with
                     | |- Markers.split (?P /\ Markers.right ?Q) =>
                       split; [eabstract (repeat straightline) | change Q]
                     | _ => letexists
                     end); []
  | |- Markers.split ?G => change G; split
  | |- True => exact I
  | |- False \/ _ => right
  | |- _ \/ False => left
  end.

(* TODO: once we can automatically prove some calls, include the success-only version of this in [straightline] *)
Ltac straightline_call :=
  lazymatch goal with
  | |- @WeakestPrecondition.call _ ?functions ?callee _ _ _ _ =>
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
  | |- @cmd ?D ?E ?c ?F ?G ?H ?I =>
    let c' := eval cbv in c in
    change (@cmd D E (fst (c, c')) F G H I)
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
