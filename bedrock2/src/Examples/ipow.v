Ltac rdelta x :=
  match constr:(Set) with
  | _ => let x := eval unfold x in x in x
  | _ => x
  end.
Tactic Notation "eabstract" tactic3(tac) :=
  let G := match goal with |- ?G => G end in
  let pf := lazymatch constr:(ltac:(tac) : G) with ?pf => pf end in
  repeat match goal with
         | H: ?T |- _ => has_evar T;
                         clear dependent H;
                         assert_succeeds (pose pf)
         | H := ?e |- _ => has_evar e;
                         clear dependent H;
                         assert_succeeds (pose pf)
         end;
  abstract (exact_no_check pf).

Tactic Notation "tryabstract" tactic3(tac) :=
  let G := match goal with |- ?G => G end in
  unshelve (
      let pf := lazymatch open_constr:(ltac:(tac) : G) with ?pf => pf end in
      tryif has_evar pf
      then exact pf
      else eabstract exact_no_check pf);
  shelve_unifiable.
Definition invert_Some {A} (x : option A) : match x with
                                            | Some _ => A
                                            | None => unit
                                            end
  := match x with
     | Some x' => x'
     | None => tt
     end.

Set Printing Depth 999999.
Local Notation "'need!' y 's.t.' Px 'let' x ':=' v 'using' pfPx 'in' pfP" :=
  (let x := v in ex_intro (fun y => Px /\ _) x (conj pfPx pfP))
  (right associativity, at level 200, pfPx at next level,
    format "'need!'  y  's.t.'  Px  '/' 'let'  x  ':='  v  'using'  pfPx  'in'  '/' pfP").
Local Notation "'need!' x 's.t.' Px 'let' x ':=' v 'using' pfPx 'in' pfP" :=
  (let x := v in ex_intro (fun x => Px /\ _) x (conj pfPx pfP))
  (only printing, right associativity, at level 200, pfPx at next level,
    format "'need!'  x  's.t.'  Px  '/' 'let'  x  ':='  v  'using'  pfPx  'in'  '/' pfP").
Local Notation "'need!' y 's.t.' Px 'let' x ':=' v 'using' pfPx 'in' pfP" :=
  (let x := v in ex_intro (fun y => Px /\ _) x (conj pfPx pfP))
  (right associativity, at level 200, pfPx at next level,
   format "'need!'  y  's.t.'  Px  '/' 'let'  x  ':='  v  'using'  pfPx  'in'  '/' pfP")
  : type_scope.
Local Notation "'need!' x 's.t.' Px 'let' x ':=' v 'using' pfPx 'in' pfP" :=
  (let x := v in ex_intro (fun x => Px /\ _) x (conj pfPx pfP))
  (only printing, right associativity, at level 200, pfPx at next level,
   format "'need!'  x  's.t.'  Px  '/' 'let'  x  ':='  v  'using'  pfPx  'in'  '/' pfP")
  : type_scope.


Require Import bedrock2.Macros bedrock2.Syntax.
Require Import bedrock2.BasicC64Syntax bedrock2.BasicALU bedrock2.NotationsInConstr.


Import BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Existing Instance bedrock2.BasicC64Syntax.Basic_bopnames_params.
Local Coercion literal (z : Z) : expr := expr.literal z.
Local Coercion var (x : string) : expr := expr.var x.

Definition ipow := ("ipow", (["x";"e"], (["ret"]:list varname), bedrock_func_body:(
  "ret" = 1;;
  while ("e") {{
    "t" = "e" .& 1;;
    if ("t") {{ "ret" = "ret" * "x" }};;
    "e" = "e" >> 1;;
    "x" = "x" * "x";;
    cmd.unset "t"
  }}
))).

Require Import bedrock2.Semantics bedrock2.BasicC64Semantics bedrock2.Map.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
Require bedrock2.WeakestPrecondition bedrock2.WeakestPreconditionProperties.
Require bedrock2.TailRecursion.

Lemma shiftr_decreases
      (x1 : Word.word 64)
      (n : Word.wzero 64 <> x1)
  : (Word.wordToNat (Word.wrshift' x1 1) < Word.wordToNat x1)%nat.
  cbv [Word.wrshift'].
Admitted.
Lemma word_test_true w : word_test w = true -> w <> Word.wzero 64. Admitted.

Section WithT.
  Context {T : Type}.
  Fixpoint bindcmd (c : cmd) (k : cmd -> T) {struct c} : T :=
    match c with
    | cmd.cond e c1 c2 => bindcmd c1 (fun c1 => bindcmd c2 (fun c2 => let c := cmd.cond e c1 c2 in k c))
    | cmd.seq c1 c2 => bindcmd c1 (fun c1 => bindcmd c2 (fun c2 => let c := cmd.seq c1 c2 in k c))
    | cmd.while e c => bindcmd c (fun c => let c := cmd.while e c in k c)
    | c => k c
    end.
End WithT.

Definition spec_of_ipow := fun functions =>
  forall x e t m,
    WeakestPrecondition.call (fun _ => True) (fun _ => False) (fun _ _ => False) functions
      "ipow" t m [x; e]
      (fun t' m' rets => t=t'/\ m=m' /\ exists v, rets = [v]).

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
  change (bindcmd fbody (fun c : cmd => P (fname, (fargs, frets, c))));
  cbv beta iota delta [bindcmd]; intros.

Import WeakestPrecondition.
Ltac unfold1_wp_cmd e :=
  lazymatch e with
    @cmd ?params ?R ?G ?PR ?CA ?c ?t ?m ?l ?post =>
    let c := eval hnf in c in
    constr:(@cmd_body params R G PR CA (@cmd params R G PR CA) c t m l post)
  end.
Ltac unfold1_wp_cmd_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_wp_cmd G in
  change G.

Ltac unfold1_wp_expr e :=
  lazymatch e with
    @expr ?params ?m ?l ?arg ?post =>
    let arg := eval hnf in arg in
    constr:(@expr_body params m l (@expr params m l) arg post)
  end.
Ltac unfold1_wp_expr_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_wp_expr G in
  change G.

Ltac unfold1_list_map e :=
  lazymatch e with
    @list_map ?A ?B ?P ?arg ?post =>
    let arg := eval hnf in arg in
    constr:(@list_map_body A B P (@list_map A B P) arg post)
  end.
Ltac unfold1_list_map_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_list_map G in
  change G.

Ltac is_nat_literal x :=
  lazymatch x with
  | O => idtac
  | S ?x => is_nat_literal x
  end.

Ltac refine_ex :=
  hnf;
  lazymatch goal with
  | |- exists x, ?P =>
    let x := fresh x in
    refine (let x := _ in ex_intro (fun x => P) x _)
  end.

Ltac straightline_cleanup :=
  match goal with
  | x := _ |- _ =>
         assert_succeeds (clear x);
           match type of x  with
           | unit => clear x
           | bool => clear x
           | list _ => clear x
           | nat => clear x
           | word => clear x
           | map.rep => clear x
           | cmd.cmd => clear x
           | expr.expr => clear x
           end

  | |- @HList.tuple.foralls ?A ?n (fun x => ?P) =>
    let n := eval hnf in n in
    lazymatch n with
    | O => change (subst! tt for x in P)
    | S ?n' =>
      let a := fresh x in
      let y := fresh x in
      change (forall a:A, @HList.tuple.foralls A n' (fun y => subst! (PrimitivePair.pair.mk a y) for x in P))
    end
  | |- @HList.hlist.foralls ?l (fun x => ?P) =>
    let l := eval hnf in l in
    lazymatch l with
    | nil => change (subst! tt for x in P)
    | cons ?A ?ts' =>
      let a := fresh x in
      let y := fresh x in
      change (forall a:A, @HList.hlist.foralls ?ts' (fun y => subst! (PrimitivePair.pair.mk a y) for x in P))
    end
  | |- @HList.tuple.foralls ?A ?n ?P =>
    let n' := eval hnf in n in
    is_nat_literal n'; change (@HList.tuple.foralls A n' P)

  (* bad implementations of reductions that reduce let binders, user sparingly *)
  | H: PrimitivePair.pair._1 (HList.tuple.apply _ _) |- _ =>
    cbn [List.repeat Datatypes.length HList.tuple.apply PrimitivePair.pair._1 PrimitivePair.pair._2] in H
  | |- PrimitivePair.pair._1 (HList.tuple.apply _ _) =>
    cbn [List.repeat Datatypes.length HList.tuple.apply PrimitivePair.pair._1 PrimitivePair.pair._2]
  | H: HList.tuple.apply (PrimitivePair.pair._2 _ _ _) _ |- _ =>
    cbn [List.repeat Datatypes.length HList.tuple.apply PrimitivePair.pair._1 PrimitivePair.pair._2] in H
  | |- HList.tuple.apply (PrimitivePair.pair._2 _ _ _) _ =>
    cbn [List.repeat Datatypes.length HList.tuple.apply PrimitivePair.pair._1 PrimitivePair.pair._2]
  | |- context [@HList.hlist.existss] => progress (cbv beta iota delta [HList.hlist.existss])

  | |- forall _, _ => intros
  | |- let _ := _ in _ => intros
  | H: exists _, _ |- _ => destruct H
  | H: _ /\ _ |- _ => destruct H
  | x := ?y |- ?G => is_var y; subst x
  | H : ?x = ?y |- _ => constr_eq x y; clear H
  | H: ?x = ?v |- _ =>
    is_var x;
    lazymatch v with context[x] => fail | _ => idtac end;
    let x' := fresh "x" in
    rename x into x';
    simple refine (let x := v in _);
    change (x' = x) in H;
    symmetry in H;
    destruct H
  end.

Ltac straightline :=
  match goal with
  | _ => straightline_cleanup
  | |- @cmd _ _ _ _ _ ?c _ _ _ ?post =>
    let c := eval hnf in c in
    lazymatch c with
    | cmd.while _ _ => fail
    | cmd.cond _ _ _ => fail
    | _ => unfold1_wp_cmd_goal; cbv beta match delta [cmd_body]
    end
  | |- @list_map _ _ (@get _ _) _ _ => unfold1_list_map_goal; cbv beta match delta [list_map_body]
  | |- @list_map _ _ (@expr _ _ _) _ _ => unfold1_list_map_goal; cbv beta match delta [list_map_body]
  | |- @list_map _ _ _ nil _ => cbv beta match fix delta [list_map list_map_body]
  | |- @expr _ _ _ _ _ => unfold1_wp_expr_goal; cbv beta match delta [expr_body]
  | |- @dexpr _ _ _ _ _ => cbv beta delta [dexpr] (* TODO: eabstract (repeat straightline) *)
  | |- @literal _ _ _ => cbv beta delta [literal]
  | |- @get _ _ _ _ => cbv beta delta [get]
  | |- TailRecursion.enforce _ _ _ => exact (conj eq_refl eq_refl)
  | |- word_of_Z ?z = Some ?v =>
    let v := rdelta v in is_evar v; (change (word_of_Z z = Some v)); exact eq_refl
  | |- @eq (@map.rep _ _ (@locals _)) _ _ =>
    eapply SortedList.eq_value; exact eq_refl
  | |- @map.get _ _ (@locals _) _ _ = Some ?v =>
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
                     | _ => refine_ex
                     end); []
  | |- Markers.split ?G => change (G); split
  | |- True => exact I
  | |- False \/ _ => right
  | |- _ \/ False => left
  end.

Ltac show_program :=
  lazymatch goal with
  | |- @cmd ?A ?B ?C ?D ?E ?c ?F ?G ?H ?I =>
    let c' := eval cbv in c in
    change (@cmd A B C D E (fst (c, c')) F G H I)
  end.

Import TailRecursion PrimitivePair HList hlist tuple pair.

Lemma ipow_ok : forall functions, spec_of_ipow (ipow::functions).
Proof.
  bind_body_of_function ipow; cbv [spec_of_ipow].
  intros.
  hnf. (* incoming call dispatch *)
  eexists. split. exact eq_refl. (* argument initialization *)

  repeat straightline; show_program.

  refine (TailRecursion.tailrec nil [("e":Syntax.varname);"ret";"x"]
    (fun v t m e ret x => pair.mk (v = Word.wordToNat e)
    (fun t' m' e' ret' x' => t' = t /\ m' = m))
    lt _ _ tt _ _ _).

  { split. exact eq_refl. eapply SortedList.eq_value. exact eq_refl. } (* init locals *)
  { exact Wf_nat.lt_wf. }
  { repeat straightline. } (* init precondition *)
  { (* loop test *)
    repeat straightline; try show_program.
    { (* loop body *)
      refine_ex; split; [eabstract (repeat straightline)|]. (* if condition *)
      split. (* if cases, path-blasting *)
      { repeat straightline.
        { (* measure decreases *)
          cbn [interp_binop parameters] in *.
          repeat match goal with H: word_test _ = true |- _ => eapply word_test_true in H end.
          eapply shiftr_decreases. congruence. }
        { split; exact eq_refl. } }
      { repeat straightline.
        { (* measure decreases *)
          cbn [interp_binop parameters] in *.
          repeat match goal with H: word_test _ = true |- _ => eapply word_test_true in H end.
          eapply shiftr_decreases. congruence. }
        { split; exact eq_refl. } } }
    { (* end of loop *)
      split; exact eq_refl. } }

  repeat straightline.

  (* function postcondition *)
  repeat eapply conj; try exact eq_refl.
  eexists; exact eq_refl.
Defined.