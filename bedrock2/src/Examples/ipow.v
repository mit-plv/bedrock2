Ltac head expr :=
  match expr with  | ?f _ => head f
  | _ => expr
  end.
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
    | c => let c := c in k c
    end.
End WithT.

Definition spec_of_ipow := fun functions =>
  forall x e t m,
    WeakestPrecondition.call (fun _ => True) (fun _ => False) (fun _ _ => False) functions
      (fst ipow) t m [x; e]
      (fun t' m' rets => t=t'/\ m=m' /\ exists v, rets = [v]).

(* FIXME: this may reduce in the values as well *)
Ltac reduce_locals_map :=
cbv [
    locals parameters
    map.put map.get map.empty map.putmany invert_Some
    SortedListString.map
    SortedList.parameters.key SortedList.parameters.value
    SortedList.parameters.key_eqb SortedList.parameters.key_ltb
    SortedList.map SortedList.sorted SortedList.put
    SortedList.value SortedList.ok SortedList.minimize_eq_proof
    String.eqb String.ltb String.prefix
    Ascii.eqb Ascii.ltb Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect
    Ascii.N_of_ascii Ascii.N_of_digits
    BinNatDef.N.ltb BinNatDef.N.eqb BinNatDef.N.compare BinNat.N.add BinNat.N.mul
    Pos.mul Pos.add Pos.eqb Pos.ltb Pos.compare Pos.compare_cont
    Bool.bool_dec bool_rec bool_rect sumbool_rec sumbool_rect
    andb orb
  ].

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
(* FIXME: do not perform beta+iota reduction in non-recursive arguments *)
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

Ltac straightline :=
  match goal with
  | |- forall _, _ => intros
  | |- let _ := _ in _ => intros
  | x := ?y |- ?G => is_var y; subst x
  | _ => progress cbv iota beta in *
  | H: exists _, _ |- _ => destruct H
  | H: _ /\ _ |- _ => destruct H
  | H: ?x = ?v |- _ =>
    assert_succeeds (subst x);
    let x' := fresh "x" in
    rename x into x';
    simple refine (let x := v in _);
    change (x' = x) in H;
    symmetry in H;
    destruct H
  | |- @cmd _ _ _ _ _ ?c _ _ _ ?post =>
    let c := eval hnf in c in
    assert_fails (idtac; lazymatch c with cmd.while _ _ => idtac end);
    unfold1_wp_cmd_goal; cbv beta match delta [cmd_body]
  | |- @list_map _ _ (@get _ _) _ _ => unfold1_list_map_goal; cbv beta match delta [list_map_body]
  | |- @list_map _ _ (@expr _ _ _) _ _ => unfold1_list_map_goal; cbv beta match delta [list_map_body]
  | |- @expr _ _ _ _ _ => unfold1_wp_expr_goal; cbv beta match delta [expr_body]
  | |- @dexpr _ _ _ _ _ => cbv beta delta [dexpr] (* TODO: eabstract (repeat straightline) *)
  | |- @literal _ _ _ => cbv beta delta [literal]
  | |- @get _ _ _ _ => cbv beta delta [get]
  | |- word_of_Z ?z = Some ?v =>
    let v := rdelta v in is_evar v; (change (word_of_Z z = Some v)); exact eq_refl
  | |- @eq (@map.rep _ _ (@locals _)) _ _ =>
    eapply SortedList.eq_value; reduce_locals_map; exact eq_refl
  | |- @map.get _ _ (@locals _) _ _ = Some ?v =>
    let v' := rdelta v in is_evar v'; (change v with v'); exact eq_refl
  | |- ?x = ?y =>
    let y := rdelta y in is_evar y; change (x=y); exact eq_refl
  | |- ?x = ?y =>
    let x := rdelta x in is_evar x; change (x=y); exact eq_refl
  | |- ?x = ?y =>
    let x := rdelta x in let y := rdelta y in constr_eq x y; exact eq_refl
  | |- exists x, ?P =>
    let x := fresh x in refine (let x := _ in ex_intro (fun x => P) x _)
  | |- ?P /\ ?Q => refine (@conj P Q _ _)
  | |- True => exact I
  | |- False \/ _ => right
  | |- _ \/ False => left
  end.

Notation "locals! l variables! vs values! x .. y , p" :=
  (fun l => ex (fun x => .. (ex (fun y =>
    l = invert_Some (map.putmany vs (cons x .. (cons y nil) .. ) map.empty)
    /\ p)) ..))
  (at level 200, x binder, right associativity)
  : type_scope.

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

Lemma shiftr_decreases
      (x1 : Word.word 64)
      (n : Word.wzero 64 <> x1)
  : (Word.wordToNat (Word.wrshift' x1 1) < Word.wordToNat x1)%nat.
  SearchAbout Word.wrshift'.
  cbv [Word.wrshift'].
Admitted.
Lemma word_test_true w : word_test w = true -> w <> Word.wzero 64. Admitted.

Lemma ipow_ok : forall functions, spec_of_ipow (ipow::functions).
Proof.
  bind_body_of_function ipow; cbv [spec_of_ipow].
  intros x0 e0 t0 m0; hnf.
  repeat straightline. { exact eq_refl. }

  refine (let P_ := fun v t m => locals! l
    variables! ["x";"e";"ret"]
    values!      x   e   ret,
    v = Word.wordToNat e /\ t = t0 /\ m = m0 in _).
  refine (let Q_ := fun v t m => locals! l
    variables! ["x";"e";"ret"]
    values!      x   e   ret,
    t = t0 /\ m = m0 in _).
  eapply TailRecursion.tailrec with (lt:=lt) (P:=P_) (Q:=Q_).

  { exact Wf_nat.lt_wf. }
  { subst P_. repeat straightline. }
  { intros; cbv [P_ Q_] in * |-.
    repeat straightline; subst P_; subst Q_; repeat straightline.
    (* measure decreases *)
    { cbn [interp_binop parameters] in *.
      eapply word_test_true in H.
      eapply shiftr_decreases. congruence. }
    { cbn [interp_binop parameters] in *.
      eapply word_test_true in H.
      eapply shiftr_decreases. congruence. }
  }

  subst Q_; repeat straightline.
  unfold1_list_map_goal; cbv beta iota delta [list_map_body]; repeat straightline.
  exact eq_refl.

  Unshelve.
  eapply WeakestPreconditionProperties.Proper_call; cbv; intuition idtac.
Defined.