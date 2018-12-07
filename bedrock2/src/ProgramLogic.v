From coqutil.Tactics Require Import letexists eabstract rdelta.
Require Import coqutil.subst coqutil.unique bedrock2.Syntax.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.TailRecursion.

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

Notation "program_logic_goal_for_function! proc" := (ltac:(
   let x := program_logic_goal_for_function proc in exact x))
  (at level 10).

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

Require bedrock2.Map.SortedList. (* special-case eq_refl *)

Ltac straightline_cleanup :=
  match goal with
  | x := _ |- _ =>
         match type of x  with
         | Semantics.word => idtac
         | Syntax.cmd => idtac
         | Syntax.expr => idtac
         | coqutil.Map.Interface.map.rep => idtac
         | BinNums.Z => idtac
         | unit => idtac
         | bool => idtac
         | list _ => idtac
         | nat => idtac
         end;
         clear x
  | |- forall _, _ => intros
  | |- let _ := _ in _ => intros
  | |- dlet.dlet ?v (fun x => ?P) => change (let x := v in P); intros
  | H: exists _, _ |- _ => destruct H
  | H: _ /\ _ |- _ => destruct H
  | x := ?y |- ?G => is_var y; subst x
  | H: ?x = ?y |- _ => constr_eq x y; clear H
  | H: ?x = ?y |- _ => is_var x; is_var y; destruct H
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

Ltac straightline :=
  match goal with
  | _ => straightline_cleanup
  | |- @cmd _ _ _ _ _ ?c _ _ _ ?post =>
    let c := eval hnf in c in
    lazymatch c with
    | cmd.while _ _ => fail
    | cmd.cond _ _ _ => fail
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
  | |- TailRecursion.enforce ?names ?values ?map =>
    let values := eval cbv in values in
    change (TailRecursion.enforce names values map);
    exact (conj (eq_refl values) eq_refl)
  | |- Semantics.word_of_Z ?z = Some ?v =>
    let v := rdelta v in is_evar v; (change (Semantics.word_of_Z z = Some v)); exact eq_refl
  | |- @eq (@coqutil.Map.Interface.map.rep _ _ (@Semantics.locals _)) _ _ =>
    eapply SortedList.eq_value; exact eq_refl
  | |- @coqutil.Map.Interface.map.get _ _ (@Semantics.locals _) _ _ = Some ?v =>
    let v' := rdelta v in is_evar v'; (change v with v'); exact eq_refl
  | |- ?x = ?y =>
    let y := rdelta y in is_evar y; change (x=y); exact eq_refl
  | |- ?x = ?y =>
    let x := rdelta x in is_evar x; change (x=y); exact eq_refl
  | |- ?x = ?y =>
    let x := rdelta x in let y := rdelta y in constr_eq x y; exact eq_refl
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
  | |- @WeakestPrecondition.call _ _ _ _ ?functions ?callee _ _ _ _ =>
    let callee_spec := lazymatch constr:(_:spec_of callee) with ?s => s end in
    let Hcall := lazymatch goal with H: callee_spec functions |- _ => H end in
    eapply WeakestPreconditionProperties.Proper_call; cycle -1;
      [ eapply Hcall | try eabstract (solve [Morphisms.solve_proper]) .. ];
      [ .. | intros ? ? ? ?]
  end.

Ltac show_program :=
  lazymatch goal with
  | |- @cmd ?A ?B ?C ?D ?E ?c ?F ?G ?H ?I =>
    let c' := eval cbv in c in
    change (@cmd A B C D E (fst (c, c')) F G H I)
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