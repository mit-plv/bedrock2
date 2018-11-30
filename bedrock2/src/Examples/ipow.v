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
         match type of x  with
         | unit => idtac
         | bool => idtac
         | list _ => idtac
         | nat => idtac
         | word => idtac
         | map.rep => idtac
         | cmd.cmd => idtac
         | expr.expr => idtac
         end;
         clear x
  | |- forall _, _ => intros
  | |- let _ := _ in _ => intros
  | |- dlet.dlet ?v (fun x => ?P) => change (let x := v in P); intros
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
  | |- TailRecursion.enforce ?names ?values ?map =>
    let values := eval cbv in values in
    change (TailRecursion.enforce names values map);
    exact (conj (eq_refl values) eq_refl)
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

Import Word TailRecursion PrimitivePair HList hlist tuple pair.

Require Import AdmitAxiom.
Lemma word_test_true_unsigned x (H : word_test x = true) : word.unsigned x <> 0.
Proof.
  cbn [parameters word_test] in *.
  rewrite word.unsigned_eqb in H.
  rewrite word.unsigned_of_Z in H.
  cbv [word.wrap] in H.
  rewrite Z.mod_0_l in H by (intro; discriminate).
  destruct (0 =? word.unsigned x) eqn:? in *; try discriminate; clear H; [].
  eapply Z.eqb_neq in Heqb.
  congruence.
Qed.

Lemma ipow_ok : forall functions, spec_of_ipow (ipow::functions).
Proof.
  bind_body_of_function ipow; cbv [spec_of_ipow].
  intros.
  hnf. (* incoming call dispatch *)
  eexists. split. exact eq_refl. (* argument initialization *)

  repeat straightline; show_program.

  refine (TailRecursion.tailrec nil [("e":Syntax.varname);"ret";"x"]
    (fun v t m e ret x => pair.mk (v = word.unsigned e)
    (fun t' m' e' ret' x' => t' = t /\ m' = m))
    (fun n m => 0 <= n < m)
    _ _ tt _ _ _);

    cbn [HList.hlist.foralls HList.tuple.foralls
         HList.hlist.existss HList.tuple.existss
         HList.hlist.apply  HList.tuple.apply 
         HList.hlist
         List.repeat Datatypes.length
         PrimitivePair.pair._1 PrimitivePair.pair._2] in *.

  { repeat straightline. }
  { exact (Z.lt_wf _). }
  { repeat straightline. } (* init precondition *)
  { (* loop test *)
    repeat straightline; try show_program.
    { (* loop body *)
      refine_ex; split; [eabstract (repeat straightline)|]. (* if condition *)
      split. (* if cases, path-blasting *)
      { repeat straightline.
        { (* measure decreases *)
          cbn [parameters interp_binop] in *.
          eapply word_test_true_unsigned in H.
          unshelve (idtac; let pf := open_constr:(word.unsigned_range _ x0) in pose proof pf);
            [exact _|cbv; congruence|].
          repeat match goal with
                   |- context [?x] => subst x
                 end.
          rewrite ?word.unsigned_sru_nowrap,
                  ?word.unsigned_of_Z,
                  ?Z.shiftr_div_pow2
            by (cbv; congruence).
          change (2 ^ (1 mod 2 ^ 64)) with 2.
          Word.mia. }
        { split; exact eq_refl. } }
      { repeat straightline.
        { (* measure decreases *)
          cbn [parameters interp_binop] in *.
          eapply word_test_true_unsigned in H.
          unshelve (idtac; let pf := open_constr:(word.unsigned_range _ x0) in pose proof pf);
            [exact _|cbv; congruence|].
          repeat match goal with
                   |- context [?x] => subst x
                 end.
          rewrite ?word.unsigned_sru_nowrap,
                  ?word.unsigned_of_Z,
                  ?Z.shiftr_div_pow2
            by (cbv; congruence).
          change (2 ^ (1 mod 2 ^ 64)) with 2.
          Word.mia. }
        { split; exact eq_refl. } } }
    { (* end of loop *)
      split; exact eq_refl. } }

  repeat straightline.

  (* function postcondition *)
  repeat eapply conj; try exact eq_refl.
  eexists; exact eq_refl.
Defined.