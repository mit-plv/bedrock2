Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Import coqutil.Byte coqutil.Datatypes.HList.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Datatypes.Inhabited.
Require Import coqutil.Tactics.letexists coqutil.Tactics.Tactics coqutil.Tactics.rewr coqutil.Tactics.rdelta.
Require Import Coq.Program.Tactics.
Require Import coqutil.Tactics.ltac_list_ops.
Require Import coqutil.Tactics.autoforward.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require coqutil.Map.SortedListString. (* for function env, other maps are kept abstract *)
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Map.OfOptionListZ.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Array.
Require Import bedrock2.ZnWords.
Require Import bedrock2.groundcbv.
Require Import bedrock2.ptsto_bytes bedrock2.Scalars.
Require Import bedrock2.WeakestPrecondition bedrock2.ProgramLogic.
Require bedrock2.Loops.
Require Import Coq.Strings.String.
Require Import bedrock2.TacticError.
Require Import bedrock2.SepBulletPoints.
Require Import bedrock2Examples.LiveVerif.string_to_ident.
Require Import bedrock2.ident_to_string.
Require Import egg.Loader.
Require Import bedrock2.egg_lemmas.
Require Import bedrock2.find_hyp.

(* `vpattern x in H` is like `pattern x in H`, but x must be a variable and is
   used as the binder in the lambda being created *)
Ltac vpattern_in x H :=
  pattern x in H;
  lazymatch type of H with
  | ?f x => change ((fun x => ltac:(let r := eval cbv beta in (f x) in exact r)) x) in H
  end.
Tactic Notation "vpattern" ident(x) "in" ident(H) := vpattern_in x H.


Require Import coqutil.Tactics.syntactic_unify.

Ltac fold_in_goal p :=
  let h := head p in
  let p' := eval cbv beta iota delta [h] in p in
  match goal with
  | |- context C[?x] =>
    syntactic_unify p' x;
    let g := context C[p] in
    change g
  end.

Ltac fold_in_hyps p :=
  let h := head p in
  let p' := eval cbv beta iota delta [h] in p in
  match goal with
  | H: context C[?x] |- _ =>
    syntactic_unify p' x;
    let g := context C[p] in
    change g in H
  end.


(* Given an equality proof of type (LHS = RHS), and a hypothesis H containing
   a subterm of the form (marker LHS), replace (marker LHS) by markedRHS,
   without adding any occurrence of marker into the proof term (we want to
   keep proof terms marker-free).
   (marker LHS) must be convertible to LHS, and RHS must be convertible to markedRHS. *)
Ltac rewrite_in_hyp_at_marker E H marker markedRHS :=
  lazymatch type of E with
  | @eq ?T ?LHS ?RHS =>
      lazymatch type of H with
      | context C[marker LHS] =>
          eapply (rewr.rew_zoom_fw E
                    (fun x: T => ltac:(let r := context C[x] in exact r))) in H;
          let u := context C[markedRHS] in change u in H
      end
  end.
(*
Ltac rewrite_in_hyp_at_marker E H marker :=
  lazymatch type of E with
  | ?LHS = ?RHS =>
      lazymatch eval pattern (marker LHS) in H with
      | ?F (marker LHS) =>
          eapply (rewr.rew_zoom_fw E F) in H;
          let t := beta1 F (marker RHS) in
          change t in H
      end
  end.
*)

(* like `change t with u in H`, but fails if t not found, and only replaces
   the first occurrence of t *)
Ltac change1_in_hyp t u H :=
  lazymatch type of H with
  | context C[t] => let a := context C[u] in change a in H
  end.

Definition dlet{A B: Type}(rhs: A)(body: A -> B): B := body rhs.


Fixpoint ands(Ps: list Prop): Prop :=
  match Ps with
  | cons P rest => P /\ ands rest
  | nil => True
  end.

Lemma ands_nil: ands nil. Proof. cbn. auto. Qed.
Lemma ands_cons: forall [P: Prop] [Ps: list Prop], P -> ands Ps -> ands (P :: Ps).
Proof. cbn. auto. Qed.

Inductive get_option{A: Type}: option A -> (A -> Prop) -> Prop :=
| mk_get_option: forall (a: A) (post: A -> Prop), post a -> get_option (Some a) post.

#[export] Instance mem: map.map Z byte := Zkeyed_map byte.
#[export] Instance mem_ok: map.ok mem := Zkeyed_map_ok byte.

#[export] Instance locals: map.map string Z := SortedListString.map Z.
#[export] Instance locals_ok: map.ok locals := SortedListString.ok Z.

#[export] Instance env: map.map String.string
                          (list String.string * list String.string * Syntax.cmd) :=
    SortedListString.map _.
#[export] Instance env_ok: map.ok env := SortedListString.ok _.

Require Import coqutil.Datatypes.PropSet.

Module map.
  Section WithMap.
    Context {key value} {map : map.map key value}.

    Definition domain(m: map): set key :=
      fun k => map.get m k <> None.

    Context {ok : map.ok map}.
    Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.
  End WithMap.
End map.

Module Z.
  Lemma min_to_ltb_dec: forall a b, Z.min a b = if Z.ltb a b then a else b.
  Proof. intros. destruct_one_match; lia. Qed.
  Lemma min_to_leb_dec: forall a b, Z.min a b = if Z.leb a b then a else b.
  Proof. intros. destruct_one_match; lia. Qed.
  Lemma max_to_ltb_dec: forall a b, Z.max a b = if Z.ltb a b then b else a.
  Proof. intros. destruct_one_match; lia. Qed.
  Lemma max_to_leb_dec: forall a b, Z.max a b = if Z.leb a b then b else a.
  Proof. intros. destruct_one_match; lia. Qed.
End Z.

Module List.
  Section WithA.
    Context [A: Type].
    Fixpoint all_none(l: list (option A)): bool :=
      match l with
      | nil => true
      | cons (Some _) _ => false
      | cons None t => all_none t
      end.
  End WithA.

  Inductive Forall3[A B C: Type](R: A -> B -> C -> Prop)
    : list A -> list B -> list C -> Prop :=
  | Forall3_nil: Forall3 R nil nil nil
  | Forall3_cons: forall (x : A) (y : B) (z: C) lA lB lC,
      R x y z -> Forall3 R lA lB lC -> Forall3 R (x :: lA) (y :: lB) (z :: lC).

  Definition seqz(start len: Z): list Z :=
    List.map Z.of_nat (List.seq (Z.to_nat start) (Z.to_nat len)).
End List.

Definition nbits_to_nbytes(nbits: Z): Z := (Z.max 0 nbits + 7) / 8.

Lemma nbits_to_nbytes_nonneg: forall nbits, 0 <= nbits_to_nbytes nbits.
Proof. intros. unfold nbits_to_nbytes. Z.to_euclidean_division_equations. lia. Qed.

Section SepForall.
  Context {A: Type}(P: A -> mem -> Prop).
  Fixpoint sep_forall(l: list A): mem -> Prop :=
    match l with
    | nil => emp True
    | cons h t => sep (P h) (sep_forall t)
    end.
End SepForall.

Lemma sep_assoc_eq: forall (p q r: mem -> Prop),
    sep (sep p q) r = sep p (sep q r).
Proof.
  intros. eapply iff1ToEq. eapply sep_assoc.
Qed.

Definition get_or_zero(m: mem)(addr: Z): byte :=
  match map.get m addr with
  | Some b => b
  | None => Byte.x00
  end.

(* To be viewed as syntactic sugar that allows us to omit offsets in contiguous
   sepclauses. Not meant to carry proofs or further meaning. *)
Class PredicateSize(predicate: Z -> mem -> Prop)(nbytes: Z) := {}.

Definition sepapp(P1 P2: Z -> mem -> Prop)
  {ofs: Z}{H: PredicateSize P1 ofs} :=
  fun (addr: Z) => sep (P1 addr) (P2 (addr + ofs)).

Infix "*+" := sepapp (at level 36, left associativity).

Global Instance sepapp_PredicateSize(P1 P2: Z -> mem -> Prop)(sz1 sz2: Z)
  (H1: PredicateSize P1 sz1)(H2: PredicateSize P2 sz2)
  : PredicateSize (sepapp P1 P2) (sz1 + sz2) := {}.

Definition emp_at(addr: Z): mem -> Prop := emp True.
Global Instance emp_at_PredicateSize: PredicateSize emp_at 0 := {}.
Global Hint Opaque emp_at : typeclass_instances.

Definition hole(n addr: Z): mem -> Prop := emp True.
Global Instance hole_PredicateSize(n: Z): PredicateSize (hole n) n := {}.
Global Hint Opaque hole : typeclass_instances.
(* otherwise, hole_PredicateSize triggers when `emp_at_PredicateSize` should *)

Require Import Coq.Logic.FunctionalExtensionality.

Lemma sepapp_emp_at_l: forall (p: Z -> mem -> Prop), emp_at *+ p = p.
Proof.
  unfold sepapp, emp_at. intros. extensionality addr. eapply iff1ToEq.
  rewrite Z.add_0_r. eapply sep_emp_True_l.
Qed.

Lemma sepapp_emp_at_r: forall p sz (H: PredicateSize p sz), p *+ emp_at = p.
Proof.
  unfold sepapp, emp_at. intros. extensionality addr. eapply iff1ToEq.
  eapply sep_emp_True_r.
Qed.

Import ZList.
Import ZList.List.ZIndexNotations.
Local Open Scope zlist_scope.

(* Type aliases that can inform proof automation, typeclass search,
   as well as humans on intended usage: *)
Definition uint_t(nbits: Z) := Z.
Definition array_t(tp: Type)(nElems: Z) := list tp.

Global Hint Opaque uint_t array_t : typeclass_instances.

Definition RepPredicate(T: Type) := T -> Z -> mem -> Prop.
Existing Class RepPredicate.

Lemma sepapp_assoc(P1 P2 P3: Z -> mem -> Prop){sz1 sz2: Z}
  {Hsz1: PredicateSize P1 sz1}{Hsz2: PredicateSize P2 sz2}:
  sepapp (sepapp P1 P2) P3 = sepapp P1 (sepapp P2 P3).
Proof.
  unfold sepapp. extensionality addr.
  rewrite sep_assoc_eq. rewrite Z.add_assoc.
  reflexivity.
Qed.

Definition array_rec{T: Type}(elem: T -> Z -> mem -> Prop)(elemSize: Z):
  list T -> Z -> mem -> Prop :=
  fix rec xs start :=
    match xs with
    | nil => emp True
    | cons h tl => sep (elem h start) (rec tl (start + elemSize))
    end.

Definition array{T: Type}(elem: RepPredicate T)(n: Z){elemSize: Z}
  {H: forall v, PredicateSize (elem v) elemSize}(vs: list T)(addr: Z): mem -> Prop :=
  sep (emp (len vs = n)) (array_rec elem elemSize vs addr).

Global Instance array_PredicateSize{T: Type}(elem: T -> Z -> mem -> Prop)(n: Z)
  (elemSize: Z)(H: forall v, PredicateSize (elem v) elemSize)
  (vs: array_t T n):
  PredicateSize (array elem n vs) (elemSize * n) := {}.

Global Hint Extern 1 (PredicateSize (array ?elem ?n ?vs) _) =>
         lazymatch type of vs with
         | list ?T => exact (@array_PredicateSize T elem n _ _ vs)
         end
         : typeclass_instances.

(* don't add this instance, otherwise terms that should be syntactically equal
     will differ in which of the two instances they use!
Global Instance array_PredicateSize_list{T: Type}(elem: T -> Z -> mem -> Prop)(n: Z)
  (elemSize: Z)(H: forall v, PredicateSize (elem v) elemSize)
  (vs: list T):
  PredicateSize (array elem n vs) (elemSize * n) := {}. *)

Lemma array_app{T: Type}(elem: T -> Z -> mem -> Prop){elemSize: Z}
  {Hsz: forall v, PredicateSize (elem v) elemSize}
  (n n1 n2: Z)(vs vs1 vs2: list T):
  n = n1 + n2 ->
  vs = vs1 ++ vs2 ->
  array elem n vs = sepapp (array elem n1 vs1) (array elem n2 vs2).
Proof.
  intros.
Abort.

Lemma array_cons{T: Type}(elem: T -> Z -> mem -> Prop){elemSize: Z}
  {Hsz: forall v, PredicateSize (elem v) elemSize}
  (n: Z)(v: T)(vs: list T):
  array elem n (v :: vs) = sepapp (elem v) (array elem (n-1) vs).
Proof.
  unfold sepapp. extensionality addr.
  unfold array.
  change (array_rec elem elemSize (v :: vs) addr) with
    (sep (elem v addr) (array_rec elem elemSize vs (addr + elemSize))).
  eapply iff1ToEq.
  cancel. cbn [seps]. unfold iff1, emp.
  replace (len (v :: vs)) with (len vs + 1) in *.
  2: {
    rewrite List.length_cons. lia.
  }
  intro m'; split; intros H; fwd.
  - ssplit; try lia. reflexivity.
  - ssplit; try lia. reflexivity.
Qed.

Lemma array_split(i: Z)[T: Type](elem: T -> Z -> mem -> Prop){elemSize: Z}
  {Hsz: forall v, PredicateSize (elem v) elemSize}
  (n: Z)(vs: list T):
  (* TODO might need arithmetic preconditions *)
  array elem n vs = sepapp (array elem i vs[:i]) (array elem (n-i) vs[i:]).
Proof.
  intros.
Admitted.

Section WithParams.
  Context {width: Z}.

  Definition wwrap{BW: Bitwidth width}(z: Z): Z := z mod 2 ^ width.
  Definition wswrap{BW: Bitwidth width}(z: Z): Z := (z + 2 ^ (width - 1)) - 2 ^ (width - 1).

  Definition access_len{BW: Bitwidth width}(sz: access_size): Z :=
    match sz with
    | access_size.one => 1
    | access_size.two => 2
    | access_size.four => 4
    | access_size.word => bytes_per_word width
    end.

  Context {BW: Bitwidth width}.

  Definition wadd(a b: Z): Z := wwrap (a + b).
  Definition wsub(a b: Z): Z := wwrap (a - b).
  Definition wmul(a b: Z): Z := wwrap (a * b).
  Definition wmulhuu(a b: Z): Z := wwrap ((a * b) / 2 ^ width).
  Definition wdivu(a b: Z): Z := wwrap (wwrap a / wwrap b).
  Definition wremu(a b: Z): Z := wwrap (Z.rem (wwrap a) (wwrap b)).
  Definition wand(a b: Z): Z := wwrap (Z.land a b).
  Definition wor(a b: Z): Z := wwrap (Z.lor a b).
  Definition wxor(a b: Z): Z := wwrap (Z.lxor a b).
  Definition wsru(a b: Z): Z := wwrap (Z.shiftr a (wwrap b)).
  Definition wslu(a b: Z): Z := wwrap (Z.shiftl a (wwrap b)).
  Definition wsrs(a b: Z): Z := wwrap (Z.shiftr (wswrap a) (wwrap b)).
  Definition wlts(a b: Z): Z := if Z.ltb (wswrap a) (wswrap b) then 1 else 0.
  Definition wltu(a b: Z): Z := if Z.ltb (wwrap a) (wwrap b) then 1 else 0.
  Definition weq(a b: Z): Z := if Z.eqb (wwrap a) (wwrap b) then 1 else 0.

  Lemma wwrap_small: forall a, 0 <= a < 2 ^ width -> wwrap a = a.
  Proof. intros. unfold wwrap. apply Z.mod_small. assumption. Qed.

  Lemma const_in_bounds: forall c: Z,
      andb (Z.leb 0 c) (Z.ltb c (2 ^ 32)) = true ->
      0 <= c < 2 ^ width.
  Proof. intros. destruct width_cases; subst width; lia. Qed.

  Definition addr_seq(start len: Z): list Z :=
    List.map (wadd start) (List.seqz 0 len).

  Definition get_seq(start len: Z)(m: mem): list byte :=
    List.map (get_or_zero m) (addr_seq start len).

  Definition byteseq_predicate(nbytes: Z)(P: list byte -> Prop)
    (addr: Z)(m: mem): Prop :=
    map.domain m = PropSet.of_list (List.seqz addr nbytes) /\
    P (get_seq addr nbytes m).

  Definition uint(nbits: Z)(v: uint_t nbits (*=Z*)): Z -> mem -> Prop :=
    byteseq_predicate (nbits_to_nbytes nbits) (fun bs => LittleEndianList.le_combine bs = v).

  (* Note: We could also provide one single generic instance like this one,
     but that creates (nbits_to_nbytes nbits) terms everywhere, so we prefer
     adding one instance per integer size, so that the size is in simplified
     from the very beginning.
  Global Instance uint_PredicateSize(nbits: Z)(v: uint_t nbits):
    PredicateSize (uint nbits v) (nbits_to_nbytes nbits) := {}. *)

  Global Instance uint_8_PredicateSize(v: uint_t 8):
    PredicateSize (uint 8 v) 1 := {}.
  Global Instance uint_16_PredicateSize(v: uint_t 16):
    PredicateSize (uint 16 v) 2 := {}.
  Global Instance uint_32_PredicateSize(v: uint_t 32):
    PredicateSize (uint 32 v) 4 := {}.
  Global Instance uint_64_PredicateSize(v: uint_t 64):
    PredicateSize (uint 64 v) 8 := {}.
  Global Instance uint_width_PredicateSize(v: uint_t width):
    PredicateSize (uint width v) width
    | 50 (* higher cost so that concrete instances are preferred *) := {}.

  Fixpoint le_combine_z(bytes: list Z): Z :=
    match bytes with
    | nil => 0
    | h :: t => Z.lor h (Z.shiftl (le_combine_z t) 8)
    end.

  Axiom TODO: False.

  Lemma bytes_to_uint: forall L nbits (bs: array_t (uint_t 8) L),
      len bs = L -> (* <-- Note: already asserted by LHS, but not by RHS *)
      array (uint 8) L bs = uint nbits (le_combine_z bs).
  Proof.
    unfold array_t in *. intros.
    remember (Z.to_nat L) as nbytes eqn: E.
    eapply (f_equal Z.of_nat) in E. rewrite Z2Nat.id in E by lia. subst L.
    revert nbytes bs E.
    induction nbytes; intros;
      extensionality addr; extensionality m;
      apply PropExtensionality.propositional_extensionality.
    - unfold array. unfold uint, byteseq_predicate. simpl in E.
      rewrite <- E.
      destruct bs; try discriminate.
      simpl. change (nbits_to_nbytes 0) with 0 in *.
      split; intros.
      + eapply sep_emp_l in H. fwd.
        case TODO.
      + fwd. eapply sep_emp_l.
        case TODO.
    - destruct bs; try discriminate.
      rewrite array_cons.
      replace (len (u :: bs) - 1) with (len bs) by (rewrite List.length_cons; lia).
      rewrite IHnbytes by (rewrite List.length_cons in *; lia).

      (* TODO... *)
  Admitted.

  Definition interp_binop(bop : bopname): Z -> Z -> Z :=
    match bop with
    | bopname.add => wadd
    | bopname.sub => wsub
    | bopname.mul => wmul
    | bopname.mulhuu => wmulhuu
    | bopname.divu => wdivu
    | bopname.remu => wremu
    | bopname.and => wand
    | bopname.or => wor
    | bopname.xor => wxor
    | bopname.sru => wsru
    | bopname.slu => wslu
    | bopname.srs => wsrs
    | bopname.lts => wlts
    | bopname.ltu => wltu
    | bopname.eq => weq
    end.

  Import bedrock2.Syntax.

  Axiom dexpr: mem -> locals -> expr -> Z -> Prop.

  (* TODO later also add dexpr_signed, whose range is -2^(width-1)..2^(width-1),
     (so we'll have 3 interpreters: to unsigned, to signed, and to Prop,
     and each operator decides which one to invoke for its arguments *)

  Axiom dexpr_range: forall m l e v, dexpr m l e v -> 0 <= v < 2 ^ width.

  Lemma dexpr_literal: forall (m: mem) (l: locals) z,
      0 <= z < 2 ^ width ->
      dexpr m l (expr.literal z) z.
  Admitted.

  Lemma dexpr_var: forall m l x (v: Z),
      map.get l x = Some v ->
      0 <= v < 2 ^ width ->
      dexpr m l (expr.var x) v.
  Proof.
  Admitted.

  (* Note: no conversion needed between v in sepclause and v returned,
     and sep already enforces bounds on v *)
  Lemma dexpr_load: forall m l e addr sz v R,
      dexpr m l e addr ->
      sep (uint match sz with
                | access_size.one => 8
                | access_size.two => 16
                | access_size.four => 32
                | access_size.word => width
                end v addr) R m ->
      dexpr m l (expr.load sz e) v.
  Proof.
  Admitted.

  (* TODO later: dexpr_inlinetable *)

  Lemma dexpr_binop: forall m l op e1 e2 (v1 v2: Z),
      dexpr m l e1 v1 ->
      dexpr m l e2 v2 ->
      dexpr m l (expr.op op e1 e2) (interp_binop op v1 v2).
  Admitted.

  Definition dexpr_binop_unf :=
    ltac:(let T := type of dexpr_binop in
          let Tu := eval unfold interp_binop in T in
          exact (dexpr_binop: Tu)).

  Lemma dexpr_ite: forall m l e1 e2 e3 (b v: Z),
      dexpr m l e1 b ->
      dexpr m l (if Z.eqb b 0 then e3 else e2) v ->
      dexpr m l (expr.ite e1 e2 e3) v.
  Admitted.

  (* Like dexpr, but with an additional P that needs to hold. P tags along
     because it doesn't want to miss the updates to the symbolic state that
     evaluating e might make. *)
  Inductive dexpr1(m: mem)(l: locals)(e: expr)(v: Z)(P: Prop): Prop :=
  | mk_dexpr1(Hde: dexpr m l e v)(Hp: P).

  Lemma dexpr1_literal: forall (m: mem) (l: locals) z (P: Prop),
      0 <= z < 2 ^ width -> P -> dexpr1 m l (expr.literal z) z P.
  Proof.
    intros. constructor. 2: assumption. eapply dexpr_literal. assumption.
  Qed.

  Lemma dexpr1_var: forall m l x (v: Z) (P: Prop),
      map.get l x = Some v ->
      0 <= v < 2 ^ width ->
      P ->
      dexpr1 m l (expr.var x) v P.
  Proof.
    intros. constructor. 2: assumption. eapply dexpr_var; assumption.
  Qed.

  Lemma dexpr1_load: forall m l e addr sz v (R: mem -> Prop) (P: Prop),
      dexpr1 m l e addr (sep (uint match sz with
                                   | access_size.one => 8
                                   | access_size.two => 16
                                   | access_size.four => 32
                                   | access_size.word => width
                                   end v addr) R m /\ P) ->
      dexpr1 m l (expr.load sz e) v P.
  Proof.
    intros. inversion H. clear H. fwd. constructor. 2: assumption.
    eapply dexpr_load; eassumption.
  Qed.

  (* TODO later: dexpr1_inlinetable *)

  Lemma dexpr1_binop: forall m l op e1 e2 (v1 v2: Z) P,
      dexpr1 m l e1 v1 (dexpr1 m l e2 v2 P) ->
      dexpr1 m l (expr.op op e1 e2) (interp_binop op v1 v2) P.
  Proof.
    intros.
    inversion H. clear H. inversion Hp. clear Hp.
    constructor. 2: assumption. eapply dexpr_binop; assumption.
  Qed.

  Definition dexpr1_binop_unf :=
    ltac:(let T := type of dexpr1_binop in
          let Tu := eval unfold interp_binop in T in
          exact (dexpr1_binop: Tu)).

  Definition bool_expr_branches(b: bool)(Pt Pf Pa: Prop): Prop :=
    (if b then Pt else Pf) /\ Pa.

  (* `dexpr_bool3 m l e c Ptrue Pfalse Palways` means "expression e evaluates to
     boolean c and if c is true, Ptrue holds, if c is false, Pfalse holds, and
     Palways always holds".
     The three Props Ptrue, Pfalse, Palways are included so that changes made to
     the symbolic state while evaluating e are still visible when continuing the
     evaluation of the program as specified by the three Props.
     They are split into three Props rather than one in order to propagate changes
     to the symbolic state made while evaluating the condition of an if into the
     then and else branches. *)
  Inductive dexpr_bool3(m: mem)(l: locals)(e: expr): bool -> Prop -> Prop -> Prop -> Prop :=
    mk_dexpr_bool_prop: forall (v: Z) (c: bool) (Ptrue Pfalse Palways: Prop),
      dexpr m l e v ->
      c = negb (Z.eqb v 0) ->
      (if c then Ptrue else Pfalse) ->
      Palways ->
      dexpr_bool3 m l e c Ptrue Pfalse Palways.

  Definition save_mem_hyp(P: mem -> Prop)(m: mem): Prop := P m.
  Definition new_mem_hyp(P: mem -> Prop)(m: mem): Prop := P m.

  Lemma dexpr_not: forall m l e b (St Sf: mem -> Prop) (Pt Pf Pa: Prop),
      dexpr_bool3 m l e b
        (save_mem_hyp St m)
        (save_mem_hyp Sf m)
        (bool_expr_branches (negb b) (new_mem_hyp Sf m -> Pt) (new_mem_hyp St m -> Pf) Pa) ->
      dexpr_bool3 m l (expr.not e) (negb b) Pt Pf Pa.
  Proof.
    intros. inversion H. clear H. subst.
    rewrite Bool.negb_involutive in *. unfold bool_expr_branches in *. fwd.
    econstructor.
    - eapply dexpr_binop. 1: eassumption.
      eapply dexpr_literal.
      destruct width_cases; subst width; better_lia.
    - cbn. unfold weq, wwrap.
      pose proof (dexpr_range _ _ _ _ H0). rewrite Z.mod_small by assumption.
      rewrite Z.mod_small by (destruct width_cases; subst width; try better_lia).
      destruct_one_match; reflexivity.
    - unfold save_mem_hyp in *.
      destr (Z.eqb v 0); eauto.
    - assumption.
  Qed.

  (* note how each of Pt, Pf, Pa is only mentioned once in the hyp, and that Pt is
     as deep down as possible, so that it can see all memory modifications once it
     gets proven *)
  Lemma dexpr_lazy_and: forall m l e1 e2 (b1 b2: bool) (Pt Pf Pa: Prop),
      dexpr_bool3 m l e1 b1
        (dexpr_bool3 m l e2 b2 Pt True True)
        True
        (bool_expr_branches (andb b1 b2) True Pf Pa) ->
      dexpr_bool3 m l (expr.lazy_and e1 e2) (andb b1 b2) Pt Pf Pa.
  Proof.
    intros.
    inversion H; subst. clear H. unfold bool_expr_branches in *. fwd.
    destruct (Z.eqb v 0) eqn: E.
    - econstructor; [eapply dexpr_ite; [eassumption | rewrite E ] | auto .. ].
      1: eapply dexpr_literal. 1: eapply const_in_bounds. all: reflexivity.
    - cbn in *. subst.
      inversion H2. clear H2 H5. subst.
      econstructor.
      1: eapply dexpr_ite. 1: eassumption. 1: rewrite E.
      1: eapply dexpr_binop. 1: eapply dexpr_literal. 1: eapply const_in_bounds.
      2: eassumption. 1: reflexivity.
      { cbn. unfold wltu, wwrap. rewrite Zmod_0_l.
        apply_in_hyps dexpr_range.
        rewrite Z.mod_small by eassumption.
        destruct_one_match; lia. }
      { destruct_one_match; auto. }
      { assumption. }
  Qed.

  Lemma dexpr_lazy_or: forall m l e1 e2 (b1 b2: bool) (Sff: mem -> Prop) (Pt Pf Pa: Prop),
      dexpr_bool3 m l e1 b1
        True
        (dexpr_bool3 m l e2 b2 True (save_mem_hyp Sff m) True)
        (bool_expr_branches (orb b1 b2) Pt (new_mem_hyp Sff m -> Pf) Pa) ->
      dexpr_bool3 m l (expr.lazy_or e1 e2) (orb b1 b2) Pt Pf Pa.
  Proof.
    intros.
    inversion H; subst. clear H. unfold bool_expr_branches, save_mem_hyp in *. fwd.
    destruct (Z.eqb v 0) eqn: E.
    - cbn in *.
      inversion H2. subst. clear H2 H4.
      econstructor. 1: eapply dexpr_ite. 1: eassumption. 1: rewrite E.
      1: eapply dexpr_binop. 1: eapply dexpr_literal. 1: eapply const_in_bounds; reflexivity.
      1: eassumption.
      1: cbn.
      2: destruct (Z.eqb v0 0); cbn; auto. 2: assumption.
      unfold wltu, wwrap. rewrite Zmod_0_l.
      eapply dexpr_range in H.
      rewrite Z.mod_small by eassumption.
      destruct_one_match; lia.
    - cbn in *.
      econstructor. 3,4: eassumption.
      1: eapply dexpr_ite. 1: eassumption. 1: rewrite E.
      1: eapply dexpr_literal. 1: eapply const_in_bounds; reflexivity.
      reflexivity.
  Qed.

  Lemma dexpr_ltu_old: forall m l e1 e2 v1 v2 (Pt Pf Pa: Prop),
      dexpr m l e1 v1 ->
      dexpr m l e2 v2 ->
      (v1 < v2 -> Pt) ->
      (v2 <= v1 -> Pf) ->
      Pa ->
      dexpr_bool3 m l (expr.op bopname.ltu e1 e2) (Z.ltb v1 v2) Pt Pf Pa.
  Proof.
    intros.
    econstructor.
    - eapply dexpr_binop; eassumption.
    - eapply dexpr_range in H.
      eapply dexpr_range in H0.
      cbn; unfold wltu, wwrap.
      rewrite 2Z.mod_small by eassumption.
      destr ((v1 <? v2)%Z); split; Lia.lia.
    - destruct_one_match; auto.
    - assumption.
  Qed.

  Lemma dexpr_eq_old: forall m l e1 e2 v1 v2 (Pt Pf Pa: Prop),
      dexpr m l e1 v1 ->
      dexpr m l e2 v2 ->
      (v1 = v2 -> Pt) ->
      (v1 <> v2 -> Pf) ->
      Pa ->
      dexpr_bool3 m l (expr.op bopname.eq e1 e2) (Z.eqb v1 v2) Pt Pf Pa.
  Proof.
    intros.
    econstructor.
    - eapply dexpr_binop; eassumption.
    - cbn. unfold weq, wwrap.
      eapply dexpr_range in H.
      eapply dexpr_range in H0.
      rewrite 2Z.mod_small by eassumption.
      destr ((v1 =? v2)%Z); split; Lia.lia.
    - destruct_one_match; auto.
    - assumption.
  Qed.

  (* TODO maybe avoid factor the lemmas for binary bool ops into one by using
     this definition?
  Definition interp_binop_bool(bop : bopname): Z -> Z -> bool :=
    match bop with
    | bopname.lts =>
    | bopname.ltu =>
    | bopname.eq =>
    | _ => ??
    end. *)

  Lemma dexpr_ltu: forall m l e1 e2 v1 v2 (Pt Pf Pa: Prop),
      dexpr1 m l e1 v1 (dexpr1 m l e2 v2 (bool_expr_branches (Z.ltb v1 v2) Pt Pf Pa)) ->
      dexpr_bool3 m l (expr.op bopname.ltu e1 e2) (Z.ltb v1 v2) Pt Pf Pa.
  Proof.
    intros. inversion H. clear H. inversion Hp. clear Hp. destruct Hp0.
    econstructor.
    - eapply dexpr_binop; eassumption.
    - apply_in_hyps dexpr_range.
      cbn; unfold wltu, wwrap.
      rewrite 2Z.mod_small by eassumption.
      destr ((v1 <? v2)%Z); split; Lia.lia.
    - destruct_one_match; auto.
    - assumption.
  Qed.

  Lemma dexpr_eq: forall m l e1 e2 v1 v2 (Pt Pf Pa: Prop),
      dexpr1 m l e1 v1 (dexpr1 m l e2 v2 (bool_expr_branches (Z.eqb v1 v2) Pt Pf Pa)) ->
      dexpr_bool3 m l (expr.op bopname.eq e1 e2) (Z.eqb v1 v2) Pt Pf Pa.
  Proof.
    intros. inversion H. clear H. inversion Hp. clear Hp. destruct Hp0.
    econstructor.
    - eapply dexpr_binop; eassumption.
    - cbn. unfold weq, wwrap.
      apply_in_hyps dexpr_range.
      rewrite 2Z.mod_small by eassumption.
      destr ((v1 =? v2)%Z); split; Lia.lia.
    - destruct_one_match; auto.
    - assumption.
  Qed.

  Lemma BoolSpec_expr_branches{Bt Bf: Prop}{b: bool}{H: BoolSpec Bt Bf b}(Pt Pf Pa: Prop):
      (Bt -> Pt) ->
      (Bf -> Pf) ->
      Pa ->
      bool_expr_branches b Pt Pf Pa.
  Proof.
    intros. unfold bool_expr_branches. destruct H; auto.
  Qed.

  Definition trace := list (mem * string * list Z * (mem * list Z)).

  Definition wp_cmd(fs: list (string * (list string * list string * cmd)))
    (c: cmd)(t: trace)(m: mem)(l: locals)(post: trace -> mem -> locals -> Prop): Prop.
  Admitted.

  Lemma weaken_wp_cmd: forall fs c t m l (post1 post2: _->_->_->Prop),
      wp_cmd fs c t m l post1 ->
      (forall t m l, post1 t m l -> post2 t m l) ->
      wp_cmd fs c t m l post2.
  Admitted.

  Lemma wp_set0: forall fs x e v t m l rest post,
      dexpr m l e v ->
      wp_cmd fs rest t m (map.put l x v) post ->
      wp_cmd fs (cmd.seq (cmd.set x e) rest) t m l post.
  Admitted.

  Lemma wp_store0: forall fs sz ea ev a v v_old R t m l rest (post: _->_->_->Prop),
      dexpr m l ea a ->
      dexpr m l ev v ->
      sep (uint match sz with
                | access_size.one => 8
                | access_size.two => 16
                | access_size.four => 32
                | access_size.word => width
                end v_old a) R m ->
      (forall m', sep (uint match sz with
                       | access_size.one => 8
                       | access_size.two => 16
                       | access_size.four => 32
                       | access_size.word => width
                       end v a) R m' -> wp_cmd fs rest t m' l post) ->
      wp_cmd fs (cmd.seq (cmd.store sz ea ev) rest) t m l post.
  Admitted.

  Lemma wp_set: forall fs x e v t m l rest post,
      dexpr1 m l e v (wp_cmd fs rest t m (map.put l x v) post) ->
      wp_cmd fs (cmd.seq (cmd.set x e) rest) t m l post.
  Admitted.

  Definition with_new_mem fs rest t (P: mem -> Prop) l post :=
    forall m: mem, P m -> wp_cmd fs rest t m l post.

  Lemma wp_store: forall fs sz ea ev a v v_old R t m l rest (post: _->_->_->Prop),
      dexpr1 m l ea a
        (dexpr1 m l ev v
           (sep (uint match sz with
                      | access_size.one => 8
                      | access_size.two => 16
                      | access_size.four => 32
                      | access_size.word => width
                      end v_old a) R m /\
                (with_new_mem fs rest t
                   (sep (uint match sz with
                              | access_size.one => 8
                              | access_size.two => 16
                              | access_size.four => 32
                              | access_size.word => width
                              end v a) R) l post))) ->
      wp_cmd fs (cmd.seq (cmd.store sz ea ev) rest) t m l post.
  Admitted.

  Lemma wp_if0: forall fs c thn els rest b Q1 Q2 t m l post,
      dexpr m l c b ->
      (b <> 0 -> wp_cmd fs thn t m l Q1) ->
      (b =  0 -> wp_cmd fs els t m l Q2) ->
      (forall t' m' l', b <> 0 /\ Q1 t' m' l' \/
                        b =  0 /\ Q2 t' m' l' ->
                        wp_cmd fs rest t' m' l' post) ->
      wp_cmd fs (cmd.seq (cmd.cond c thn els) rest) t m l post.
  Admitted.

  Definition sorted_varnames(l: locals): list string :=
    match l with
    | SortedList.Build_rep tuples pf => List.map fst tuples
    end.

  Lemma wp_if: forall fs c l thn els rest b Q1 Q2 t m post,
      dexpr m l c b ->
      (b <> 0 -> wp_cmd fs thn t m l (fun t' m' l' =>
                   sorted_varnames l' = sorted_varnames l /\ Q1 t' m' l')) ->
      (b =  0 -> wp_cmd fs els t m l (fun t' m' l' =>
                   sorted_varnames l' = sorted_varnames l /\ Q2 t' m' l')) ->
      (forall t' m' l', sorted_varnames l' = sorted_varnames l ->
                        (b <> 0 /\ Q1 t' m' l' \/
                         b =  0 /\ Q2 t' m' l') ->
                        wp_cmd fs rest  t' m' l' post) ->
      wp_cmd fs (cmd.seq (cmd.cond c thn els) rest) t m l post.
  Proof.
    intros. eapply wp_if0. 1: exact H. all: clear H; eauto.
    cbv beta in *.
    intros * [? | ?]; fwd; eapply H2; eauto.
  Qed.

  Definition then_branch_marker(P: Prop) := P.
  Definition else_branch_marker(P: Prop) := P.
  Definition after_if fs (b: bool) (Q1 Q2: trace -> mem -> locals -> Prop) rest post :=
    forall t m l,
      (if b then Q1 t m l else Q2 t m l) ->
      wp_cmd fs rest t m l post.

  Lemma wp_if_bool_dexpr: forall fs c thn els rest t0 m0 l0 b Q1 Q2 post,
      dexpr_bool3 m0 l0 c b
        (then_branch_marker (wp_cmd fs thn t0 m0 l0 Q1))
        (else_branch_marker (wp_cmd fs els t0 m0 l0 Q2))
        (after_if fs b Q1 Q2 rest post) ->
      wp_cmd fs (cmd.seq (cmd.cond c thn els) rest) t0 m0 l0 post.
  Proof.
    intros. inversion H. subst. clear H.
    unfold then_branch_marker, else_branch_marker, after_if in *.
    destr (Z.eqb v 0);
      (eapply wp_if0; [eassumption |intro C; try congruence; cbn in *; eauto ..]).
    all: intros * [(? & ?) | (? & ?)]; try (exfalso; congruence); eauto.
    Unshelve. all: try assumption.
  Qed.

  Lemma wp_while {measure : Type} (v0 : measure) (e: expr) (c: cmd) t (m: mem) l fs rest
    (invariant: measure -> trace -> mem -> locals -> Prop) {lt}
    {post : trace -> mem -> locals -> Prop}
    (Hpre: invariant v0 t m l)
    (Hwf : well_founded lt)
    (Hbody : forall v t m l,
      invariant v t m l ->
      exists b, dexpr_bool3 m l e b
                  (wp_cmd fs c t m l
                      (fun t m l => exists v', invariant v' t m l /\ lt v' v))
                  (wp_cmd fs rest t m l post)
                  True)
    : wp_cmd fs (cmd.seq (cmd.while e c) rest) t m l post.
  Admitted.

  (* The postcondition of the callee's spec will have a concrete shape that differs
     from the postcondition that we pass to `call`, so when using this lemma, we have
     to apply weakening for `call`, which generates two subgoals:
     1) call f t m argvals ?mid
     2) forall t' m' resvals, ?mid t' m' resvals -> the post of `call`
     To solve 1), we will apply the callee's spec, but that means that if we make
     changes to the context while solving the preconditions of the callee's spec,
     these changes will not be visible in subgoal 2
  Lemma wp_call: forall fs binds f argexprs rest t m l post,
      wp_exprs m l argexprs (fun argvals =>
        call fs f t m argvals (fun t' m' resvals =>
          get_option (map.putmany_of_list_zip binds resvals l) (fun l' =>
            wp_cmd fs rest t' m' l' post))) ->
      wp_cmd fs (cmd.seq (cmd.call binds f argexprs) rest) t m l post.
  Proof.
  Admitted.

     It's not clear whether a change to wp_call can fix this.
     Right now, specs look like this:

  Instance spec_of_foo : spec_of "foo" := fun functions =>
    forall t m argvals ghosts,
      NonmemHyps ->
      (sepclause1 * ... * sepclauseN) m ->
      WeakestPrecondition.call functions "foo" t m argvals
        (fun t' m' rets => calleePost).

  If I want to use spec_of_foo, I'll have a WeakestPrecondition.call goal with callerPost, and to
  reconcile the callerPost with calleePost, I have to apply weakening/Proper for
  WeakestPrecondition.call, which results in two sugoals:

  1) WeakestPrecondition.call "foo" t m argvals ?mid
  2) forall t' m' resvals, ?mid t' m' resvals -> callerPost

  On 1), I will apply foo_ok (which proves spec_of_foo), so all hyps in spec_of_foo are proven
  in a subgoal separate from subgoal 2), so changes made to the context won't be visible in
  subgoal 2).

  Easiest to use would be this one:

  Instance spec_of_foo' : spec_of "foo" := fun functions =>
    forall t m argvals ghosts callerPost,
      seps [sepclause1; ...; sepclauseN; emp P1; ... emp PN;
         emp (forall t' m' retvals,
                  calleePost t' m' retvals ->
                  callerPost t' m' retvals)] m ->
      WeakestPrecondition.call functions "foo" t m argvals callerPost.

  because it has weakening built in and creates only one subgoal, so all context modifications
  remain visible.
  And using some notations, this form might even become ergonomic. *)

  Lemma wp_skip: forall fs t m l (post: trace -> mem -> locals -> Prop),
      post t m l ->
      wp_cmd fs cmd.skip t m l post.
  Admitted.

  Definition vc_func fs '(innames, outnames, body) (t: trace) (m: mem) (argvs: list Z)
                     (post : trace -> mem -> list Z -> Prop) :=
    exists l, map.of_list_zip innames argvs = Some l /\
      wp_cmd fs body t m l (fun t' m' l' =>
        exists retvs, map.getmany_of_list l' outnames = Some retvs /\ post t' m' retvs).

  Definition arguments_marker(args: list Z): list Z := args.

End WithParams.

Inductive head_of_implicit_facts: Prop :=
| mk_head_of_implicit_facts.

Ltac mark_as_implicit_facts H := eapply (conj mk_head_of_implicit_facts) in H.

Declare Scope implicit_facts_scope.
Open Scope implicit_facts_scope.

Notation "(implicit facts)" := (head_of_implicit_facts /\ _) (only printing)
  : implicit_facts_scope.

Definition purify(R: mem -> Prop)(P: Prop): Prop := forall m, R m -> P.

Lemma purify_sep: forall {RHead RTail: mem -> Prop} {PHead PTail: Prop},
    purify RHead PHead ->
    purify RTail PTail ->
    purify (sep RHead RTail) (PHead /\ PTail).
Admitted.

Lemma purify_sep_skip_l: forall {RHead RTail: mem -> Prop} {PTail: Prop},
    purify RTail PTail ->
    purify (sep RHead RTail) PTail.
Admitted.

Lemma purify_sep_skip_r: forall {RHead RTail: mem -> Prop} {PHead: Prop},
    purify RHead PHead ->
    purify (sep RHead RTail) PHead.
Admitted.

Lemma purify_array{T: Type}: forall elem n (vs: list T) a elemSize
    {Hsz: forall v, PredicateSize (elem v) elemSize},
    purify (array elem n vs a) (len vs = n). (* TODO add bounds on a *)
Proof.
  unfold purify, array. intros. eapply sep_emp_l in H. apply H.
Qed.

#[export] Hint Resolve purify_array : purify.

Lemma purify_scalar{width: Z}{BW: Bitwidth width}: forall a v nbits,
    purify (uint nbits v a) (0 <= v < 2 ^ nbits /\ 0 <= a < 2 ^ width).
    (* TODO a stronger bound would be: a + nbits_to_nbytes nbits < 2 ^ width *)
Proof.
  unfold purify, uint, byteseq_predicate. intros.
  (* TODO byteseq_predicate should assert that address is in bounds *)
Admitted.

#[export] Hint Resolve purify_scalar : purify.

Ltac purify_rec :=
  lazymatch goal with
  | |- purify ?clause ?E =>
      is_evar E;
      lazymatch clause with
      | sep ?R1 ?R2 =>
          is_evar E;
          let HLeft := fresh in
          let HRight := fresh in
          tryif (eassert (purify R1 _) as HLeft by purify_rec) then
            tryif (eassert (purify R2 _) as HRight by purify_rec) then
              exact (purify_sep HLeft HRight)
            else
              refine (purify_sep_skip_r HLeft)
          else
            tryif (eassert (purify R2 _) as HRight by purify_rec) then
              exact (purify_sep_skip_l HRight)
            else
              fail "can purify" clause
      | _ => solve [eauto with purify]
      end
  | |- _ => fail "goal should be of form 'purify _ _'"
  end.

Ltac purify_hyp H :=
  lazymatch type of H with
  | ?R ?m => let HP := fresh H "P" in eassert (purify R _) as HP;
             [ purify_rec | specialize (HP m H); mark_as_implicit_facts HP ]
  end.

Ltac purify :=
  lazymatch goal with
  | H: sep _ _ _ |- _ => purify_hyp H
  end.

Inductive sized_predicate: Type :=
| mk_sized_predicate(p: Z -> mem -> Prop)(sz: Z)(Hsz: PredicateSize p sz).

Definition sized_emp := mk_sized_predicate emp_at 0 emp_at_PredicateSize.

Definition sepapp_sized_predicates(sp1 sp2: sized_predicate): sized_predicate :=
  match sp1, sp2 with
  | mk_sized_predicate p1 sz1 Hsz1, mk_sized_predicate p2 sz2 Hsz2 =>
      mk_sized_predicate (@sepapp p1 p2 sz1 Hsz1) (sz1 + sz2)
        (@sepapp_PredicateSize p1 p2 sz1 sz2 Hsz1 Hsz2)
  end.

Definition proj_sized_predicate(sp: sized_predicate): Z -> mem -> Prop :=
  match sp with
  | mk_sized_predicate p _ _ => p
  end.

Definition sepapps(l: list sized_predicate): Z -> mem -> Prop :=
  proj_sized_predicate (List.fold_left sepapp_sized_predicates l sized_emp).

Definition interp_sepapp_tree(t: Tree.Tree sized_predicate): Z -> mem -> Prop :=
  proj_sized_predicate (Tree.interp id sepapp_sized_predicates t).

Lemma flatten_eq_interp_sepapp_tree_aux(t : Tree.Tree sized_predicate):
  forall sp0: sized_predicate,
    match List.fold_left sepapp_sized_predicates (Tree.flatten t) sp0,
          sepapp_sized_predicates sp0 (Tree.interp id sepapp_sized_predicates t) with
    | mk_sized_predicate p1 sz1 Hsz1, mk_sized_predicate p2 sz2 Hsz2 =>
        p1 = p2 /\ sz1 = sz2
    end.
Proof.
  induction t; intros.
  - simpl. destruct sp0. destruct a. simpl. auto.
  - simpl. change @app with @List.app.
    rewrite List.fold_left_app.
    specialize (IHt1 sp0).
    specialize (IHt2 (List.fold_left sepapp_sized_predicates (Tree.flatten t1) sp0)).
    destruct_one_match.
    destr sp0.
    destr (List.fold_left sepapp_sized_predicates (Tree.flatten t1)
             (mk_sized_predicate p0 sz0 Hsz0)).
    destr (Tree.interp id sepapp_sized_predicates t1).
    destr (Tree.interp id sepapp_sized_predicates t2).
    simpl in *.
    fwd. subst. rewrite <- sepapp_assoc. rewrite Z.add_assoc. split; reflexivity.
Qed.

Lemma flatten_eq_interp_sepapp_tree(t : Tree.Tree sized_predicate):
  sepapps (Tree.flatten t) = interp_sepapp_tree t.
Proof.
  unfold sepapps, interp_sepapp_tree, proj_sized_predicate.
  pose proof (flatten_eq_interp_sepapp_tree_aux t sized_emp) as P.
  unfold sized_emp in *. do 2 destruct_one_match. simpl in P. apply proj1 in P.
  subst. apply sepapp_emp_at_l.
Qed.

Lemma interp_sepapp_tree_eq_of_flatten_eq(LHS RHS : Tree.Tree sized_predicate):
  Tree.flatten LHS = Tree.flatten RHS ->
  interp_sepapp_tree LHS = interp_sepapp_tree RHS.
Proof. intros. rewrite <-2flatten_eq_interp_sepapp_tree. f_equal. assumption. Qed.

Ltac pose_ZWord_lemmas :=
  pose proof wwrap_small as z_wwrap_small.

(* to make sure sep always appears with the same arity *)
Definition holds(P: mem -> Prop)(m: mem) := P m.

Ltac egg_simpl_or_prove :=
  repeat match goal with
    | H: sep ?P ?Q ?m |- _ => change (holds (sep P Q) m) in H
    end;
  try match goal with
    | |- sep ?P ?Q ?m => change (holds (sep P Q) m)
    end;
  (* seps takes (@cons (mem -> Prop) ...), and -> in terms are not supported *)
  cbn [seps] in *;
  pose_Prop_lemmas;
  pose_ZWord_lemmas;
  pose_basic_Z_lemmas;
  pose_common_list_lemmas;
  pose_zlist_lemmas;
  repeat egg_step 3.

(*
TODO: once we have C notations for function signatures,
put vernac between /*.   .*/ and ltac between /**.  .**/ so that
only Ltac gets hidden *)
Notation "'C_STARTS_HERE' /* *" := True (only parsing).
Notation "'!EOF' '.*' '*/' //" := True (only parsing).


Declare Scope live_scope.
Delimit Scope live_scope with live.
Local Open Scope live_scope.

(* Needed to know where the conditions (hypotheses) introduced by an if start,
   will be replaced by (mk_scope_marker ThenBranch) in the then branch,
   by (mk_scope_marker ElseBranch) in the else branch, and deleted in the
   code after the if. *)
Inductive temp_if_marker: Set := mk_temp_if_marker.

Inductive scope_kind := FunctionBody | ThenBranch | ElseBranch | LoopBody | LoopInvariant.
Inductive scope_marker: scope_kind -> Set := mk_scope_marker sk : scope_marker sk.

Notation "'____' sk '____'" := (scope_marker sk) (only printing) : live_scope.

Ltac assert_scope_kind expected :=
  let sk := lazymatch goal with
            | H: scope_marker ?sk |- _ => sk
            | _ => fail "no scope marker found"
            end in
  tryif constr_eq sk expected then idtac
  else fail "This snippet is only allowed in a" expected "block, but we're in a" sk "block".

Definition ready{P: Prop} := P.

Notation "l" := (arguments_marker l)
  (at level 100, only printing) : live_scope.

Ltac put_into_current_locals :=
  lazymatch goal with
  | |- wp_cmd _ _ _ _ (map.put ?l ?x ?v) _ =>
    let is_decl := lazymatch l with
                   | context[(x, _)] => false
                   | _ => true
                   end in
    let i := string_to_ident x in
    let old_i := fresh i "_0" in
    lazymatch is_decl with
    | true => idtac
    | false => rename i into old_i
    end;
    (* match again because there might have been a renaming *)
    lazymatch goal with
    | |- wp_cmd ?call ?c ?t ?m (map.put ?l ?x ?v) ?post =>
        (* tradeoff between goal size blowup and not having to follow too many aliases *)
        let v' := rdelta_var v in
        pose (i := v');
        change (wp_cmd call c t m (map.put l x i) post)
    end;
    lazymatch goal with
    | |- wp_cmd ?call ?c ?t ?m ?l ?post =>
        let keys := eval lazy in (map.keys l) in
        let values := eval hnf in
          (match map.getmany_of_list l keys with
           | Some vs => vs
           | None => nil
           end) in
        let kvs := eval unfold List.combine in (List.combine keys values) in
        change (wp_cmd call c t m (map.of_list kvs) post)
    end;
    lazymatch is_decl with
    | true => idtac
    | false => try clear old_i
    end
  end.

Inductive undoable_step: Type :=
| unfold_step{V: Type}(pred: V -> Z -> mem -> Prop).

Ltac unfold_pred pred :=
  let name := fresh "step0" in
  pose (unfold_step pred) as name;
  let h := head pred in
  repeat match goal with
    | H: context C[pred ?v] |- _ =>
        let u := eval unfold h in (pred v) in
        let t := context C[u] in
        change t in H
    | |- context C[pred ?v] =>
        let u := eval unfold h in (pred v) in
        let t := context C[u] in
        change t
    end.

Ltac undo_step :=
  lazymatch goal with
  | St := unfold_step ?pred |- _ =>
      repeat (let c := open_constr:(pred ltac:(constructor)) in fold_in_hyps c);
      clear St
  end.

(* marker for use in the conclusion: *)
Definition focus(clause: Z -> mem -> Prop)(addr: Z) := clause.
Notation "<< c >>@ a" := (focus c a)
  (at level 8, c at level 200, a at level 0, format "<< c >>@ a").

(* markers for use in the memory hypothesis: *)
(* marks a clause which is an extension of the clause focused in the goal,
   on the left & right, ie a super range of the focused range *)
Definition lr_ext_range(start size: Z)(clause: Z -> mem -> Prop) := clause.
(* marks a clause of which the clause focused in the goal is a prefix *)
Definition r_ext_range(size: Z)(clause: Z -> mem -> Prop) := clause.
Definition same_range(clause: Z -> mem -> Prop) := clause.

Notation "<< c >>@ a ..+ sz" := (lr_ext_range a sz c)
  (at level 8, c at level 200, a at level 0, sz at level 0, format "<< c >>@ a ..+ sz").
Notation "<< c >>..+ sz" := (r_ext_range sz c)
  (at level 8, c at level 200, sz at level 0, format "<< c >>..+ sz").
Notation "<< c >>" := (same_range c)
  (at level 8, c at level 200, format "<< c >>").

(* Markers to encode "program counter" of step-by-step Ltac procedure.
   If we packed several actions into one step, these markers would not be needed. *)
Definition pre_canceling(P: Prop) := P.
Definition pre_canceling_done(P: Prop) := P.

Inductive advance_focus_result := FocusNotFound | FocusAdvanced | FocusAtEnd.

(* Expects a term of the form (_ *+ (_ *+ ... _)),
   returns a pair of type (advance_focus_result * (Z -> mem -> Prop)) *)
Ltac advance_focus_in_sepapps t :=
  lazymatch t with
  | @sepapp ?hd ?tl ?hdSize ?Hsize =>
      lazymatch hd with
      | focus ?clause ?addr =>
          let newAddr := eval cbn in (Z.add addr hdSize) in
          lazymatch tl with
          | @sepapp ?second ?tltl ?secondSize ?HSecondSize =>
              constr:((FocusAdvanced,
                        @sepapp clause (@sepapp (focus second newAddr)
                                          tltl secondSize HSecondSize) hdSize Hsize))
          | _ => constr:((FocusAdvanced,
                           @sepapp clause (focus tl newAddr) hdSize Hsize))
          end
      | _ => lazymatch advance_focus_in_sepapps tl with
             | (FocusNotFound, _) => constr:((FocusNotFound, t))
             | (FocusAdvanced, ?tl') => constr:((FocusAdvanced, @sepapp hd tl' hdSize Hsize))
             | (FocusAtEnd, ?tl') => constr:((FocusAtEnd, @sepapp hd tl' hdSize Hsize))
             end
      end
  | focus ?clause ?addr => constr:((FocusAtEnd, clause))
  | _ => constr:((FocusNotFound, t))
  end.

Ltac focus_first_in_sepapps t a :=
  lazymatch t with
  | @sepapp ?hd ?tl ?hdSize ?Hsize => constr:(@sepapp (focus hd a) tl hdSize Hsize)
  | _ => constr:(focus t a)
  end.

Ltac focus_first_in_seps t :=
  lazymatch t with
  | @sep ?K ?V ?M (?hd ?hdAddr) ?tl =>
      let hd' := focus_first_in_sepapps hd hdAddr in constr:(@sep K V M (hd' hdAddr) tl)
  end.

Ltac focus_first_in_goal :=
  let t := lazymatch goal with
           | |- pre_canceling (?t ?m /\ _) => t
           | |- pre_canceling (?t ?m) => t
           | |- ?t ?m /\ _ => t
           | |- ?t ?m => t
           end in
  let t' := focus_first_in_seps t in change t with t'.

(* Note: all sep clauses except the last one (frame) are expected to have an address,
   ie to be of shape (f a) *)
Ltac advance_focus_in_seps t :=
  lazymatch t with
  | @sep ?K ?V ?M (?hd ?hdAddr) ?tl =>
      lazymatch tl with
      | @sep _ _ _ _ _ =>
          lazymatch advance_focus_in_sepapps hd with
          | (FocusNotFound, _) =>
              lazymatch advance_focus_in_seps tl with
              | (FocusNotFound, _) => constr:((FocusNotFound, t))
              | (FocusAdvanced, ?tl') => constr:((FocusAdvanced, @sep K V M (hd hdAddr) tl'))
              | (FocusAtEnd, ?tl') => constr:((FocusAtEnd, @sep K V M (hd hdAddr) tl'))
              end
          | (FocusAdvanced, ?hd') => constr:((FocusAdvanced, @sep K V M (hd' hdAddr) tl))
          | (FocusAtEnd, ?hd') =>
              let tl' := focus_first_in_seps tl in
              constr:((FocusAdvanced, @sep K V M (hd' hdAddr) tl'))
          end
      | ?Frame =>
          lazymatch advance_focus_in_sepapps hd with
          | (FocusNotFound, _) => constr:((FocusNotFound, t))
          | (FocusAdvanced, ?hd') => constr:((FocusAdvanced, @sep K V M (hd' hdAddr) tl))
          | (FocusAtEnd, ?hd') => constr:((FocusAtEnd, @sep K V M (hd' hdAddr) tl))
          end
      end
  end.

Ltac advance_focus_in_goal :=
  let t := lazymatch goal with
           | |- pre_canceling (?t ?m /\ _) => t
           | |- pre_canceling (?t ?m) => t
           | |- ?t ?m /\ _ => t
           | |- ?t ?m => t
           end in
  lazymatch advance_focus_in_seps t with
  | (FocusNotFound, _) => fail "focus not found"
  | (FocusAdvanced, ?t') => change t with t'
  | (FocusAtEnd, ?t') => change t with t'; change pre_canceling with pre_canceling_done
  end.

Ltac unfold_pred_at_focus :=
  match goal with
  | |- context C[focus (?pred ?v) ?addr] =>
      let name := fresh "step0" in
      pose (unfold_step pred) as name;
      let h := head pred in
      let u := eval unfold h in (pred v) in
      let u' := focus_first_in_sepapps u addr in
      let g := context C[u'] in
      change g
  end.

Ltac get_predicate_size pred :=
  let pf := constr:(_ : PredicateSize pred _) in
  lazymatch type of pf with
  | PredicateSize _ ?sz => sz
  end.

Ltac has_inductive_type e :=
  let t := type of e in
  tryif (let h := head t in is_ind h) then idtac
  else tryif (let r := eval red in t in
              let h := head r in
              is_ind h) then idtac
    else fail "type of" e "is not inductive".

Ltac is_ground_head e :=
  match e with
  | _ => is_const e
  | _ => is_constructor e
  | _ => is_ind e
  | _ => fail "term" e "is not ground"
  end.

Ltac is_ground_app e :=
  lazymatch e with
  | ?f ?a => is_ground_app f; is_ground_app a
  | _ => is_ground_head e
  end.

Ltac is_cbv_safe e :=
  has_inductive_type e;
  is_ground_app e.

Ltac cbv_if_safe e :=
  match constr:(Set) with
  | _ => let __ := match constr:(Set) with
                   | _ => is_cbv_safe e
                   end in
         eval cbv in e
  | _ => e
  end.

Ltac symbolic_compare_prover :=
  (* Don't do this unfold because it exposes a Z.max that makes lia/zify choke:
     https://github.com/coq/coq/issues/16475 *)
  (* unfold nbits_to_nbytes in *; *)
  lia.

(* returns a comparison (Eq | Lt | Gt) or fails if uncomparable *)
Ltac compareZ a b :=
  match constr:(Set) with
  | _ => let __ := match constr:(Set) with
                   | _ => assert_succeeds (constr_eq a b)
                   end in
         constr:(Eq)
  | _ => let __ := match constr:(Set) with
                   | _ => is_cbv_safe a; is_cbv_safe b
                   end in
         let r := eval cbv in (Z.compare a b) in constr:(r)
  | _ => let __ := match constr:(Set) with
                   | _ => assert_succeeds (assert (a < b) by symbolic_compare_prover)
                   end in
         constr:(Lt)
  | _ => let __ := match constr:(Set) with
                   | _ => assert_succeeds (assert (a = b) by symbolic_compare_prover)
                   end in
         constr:(Eq)
  | _ => let __ := match constr:(Set) with
                   | _ => assert_succeeds (assert (a > b) by symbolic_compare_prover)
                   end in
         constr:(Gt)
  | _ => fail 1 "can't compare" a "and" b
  end.

(* returns true if a=b, false if a<>b, or fails if it is unclear *)
Ltac eqZ a b :=
  lazymatch compareZ a b with
  | Eq => constr:(true)
  | _ => constr:(false)
  end.

Ltac pre_cancel_step :=
  lazymatch goal with
  | H: sep _ _ ?m |- pre_canceling (?SEPS ?m /\ ?Rest) =>
      lazymatch SEPS with
      | context[focus ?pred ?start] =>
          let size := get_predicate_size pred in
          lazymatch type of H with (* cases apply in bottom-up order *)

          (* if the focused clause in H and the focused clause in the goal already
             have the same start address AND the same size: *)
          | context[same_range ?pred'] =>
              tryif syntactic_unify pred pred' then
                change (same_range pred') with pred' in H;
                advance_focus_in_goal
              else
                lazymatch pred' with
                | array ?elem' ?L' ?vs' =>
                    lazymatch pred with
                    | array ?elem ?L ?vs =>
                        tryif syntactic_unify elem elem' then
                          tryif syntactic_unify vs vs' then
                            tryif is_cbv_safe L; is_cbv_safe L' then
                              let cL := eval cbv in L in
                              let cL' := eval cbv in L' in
                              tryif constr_eq cL cL'
                              then change (focus pred start) with
                                          (focus (array elem cL vs) start);
                                   change (same_range pred') with
                                          (array elem' cL' vs') in H;
                                   advance_focus_in_goal
                              else fail "expected" pred "and" pred'
                                     "to have same length, but they don't!"
                            else fail "TODO: unify non-cbv-safe lengths"
                          else fail "TODO: unify array values"
                        else fail "TODO: support for arrays of different elements"
                    | uint ?nbits ?v =>
                        rewrite_in_hyp_at_marker
                          (bytes_to_uint L' nbits vs'
                             ltac:((repeat rewrite List.len_from; lia))) H
                          same_range
                          (same_range (uint nbits (le_combine_z vs')))
                    | _ => unfold_pred_at_focus; (* also focuses on first sepapp clause *)
                           change (same_range pred') with (r_ext_range size pred') in H
                    end
                end

          (* if the focused clause in H and the focused clause in the goal already
             have the same start address, split the focused clause in H so that it
             has the same length as the focused clause in the goal: *)
          | context[r_ext_range ?size' ?pred'] =>
              lazymatch eqZ size size' with
              | true => change (r_ext_range size' pred') with (same_range pred') in H
              | false =>
                  lazymatch pred' with
                  | array ?epred' ?L' ?vs' =>
                      (* TODO don't confuse array lengths and byte counts *)
                      let csize := cbv_if_safe size in
                      let rhslen := cbv_if_safe (L'-csize) in
                      rewrite_in_hyp_at_marker
                        (array_split csize epred' L' vs') H
                        (r_ext_range size')
                        (sepapp (same_range (array epred' csize vs'[:csize]))
                                (array epred' rhslen vs'[csize:]))
                  | _ => fail "TODO support for splitting non-array hyp"
                  end
              end

          (* split the clause in H so that its start matches the start of the focused
             clause in the goal (or if already split, move the focus in the hyp): *)
          | context[lr_ext_range ?start' ?size' ?pred'] =>
              lazymatch eqZ start start' with
              | true => change (lr_ext_range start' size' pred')
                  with (r_ext_range size' pred') in H
              | false =>
                  lazymatch pred' with
                  | array _ _ _ => fail "TODO: support for splitting array to match start"
                  | @sepapp ?hd ?tl ?hdSize ?Hsz =>
                      lazymatch compareZ (start'+hdSize) start with
                      | Lt => change (lr_ext_range start' size' pred') with
                          (@sepapp hd (lr_ext_range (start'+hdSize) (size'-hdSize) tl)
                             hdSize Hsz) in H
                      | Eq => change (lr_ext_range start' size' pred') with
                          (@sepapp hd (r_ext_range (size'-hdSize) tl) hdSize Hsz) in H
                      | Gt => fail "TODO support for splitting to match start"
                      end
                  | _ => fail "TODO: support for splitting things other than array or sepapp"
                  end
              end

          (* find and mark a clause of which the clause focused in the goal is a subrange: *)
          | _ => match type of H with
                 | context[sep (?pred' ?start') _] =>
                     let size' := get_predicate_size pred' in
                     assert_succeeds (
                         assert (start' <= start /\ start+size <= start'+size')
                         by (cbn; lia));
                    change pred' with (lr_ext_range start' size' pred') in H
                 end
          end

      | _ => focus_first_in_goal
      end
  end.

Ltac start :=
  lazymatch goal with
  | |- {_: prod (prod (list string) (list string)) Syntax.cmd & _ } => idtac
  | |- _ => fail "goal needs to be of shape {_: list string * list string * Syntax.cmd & _ }"
  end;
  let eargnames := open_constr:(_: list string) in
  refine (existT _ (eargnames, _, _) _);
  let fs := fresh "fs" in
  intro fs;
  let n := fresh "Scope0" in pose proof (mk_scope_marker FunctionBody) as n;
  intros;
  (* since the arguments will get renamed, it is useful to have a list of their
     names, so that we can always see their current renamed names *)
  let arguments := fresh "arguments" in
  lazymatch goal with
  | |- vc_func _ ?f ?t ?m ?argvalues ?post =>
    pose (arguments_marker argvalues) as arguments;
    let argnames := map_with_ltac varconstr_to_string argvalues in
    unify eargnames argnames;
    move arguments before n
  end;
  unfold vc_func;
  lazymatch goal with
  | |- exists l, map.of_list_zip ?keys ?values = Some l /\ _ =>
    let kvs := eval unfold List.combine in (List.combine keys values) in
    exists (map.of_list kvs);
    split; [reflexivity| ]
  end.

(* Note: contrary to add_last_var_to_post, this one makes Post a goal rather
   than a hypothesis, because if it was a hypothesis, it wouldn't be possible
   to clear vars *)
Ltac add_last_hyp_to_post :=
  let last_hyp := match goal with H: _ |- _ => H end in
  let T := type of last_hyp in
  lazymatch T with
  | scope_marker _ => fail "done (scope marker reached)"
  | _ ?m => let t := type of m in
            lazymatch t with
            | @map.rep (@word.rep _ _) Init.Byte.byte _ => flatten_seps_in last_hyp
            | _ => idtac
            end
  | _ => idtac
  end;
  lazymatch type of T with
  | Prop => refine (ands_cons last_hyp _); clear last_hyp
  | _ => clear last_hyp
  end.

Ltac is_in_post_evar_scope x :=
  lazymatch goal with
  | |- ?E ?T ?M ?L =>
      lazymatch type of E with
      | ?Trace -> ?Mem -> ?Locals -> Prop =>
          assert_succeeds (unify E (fun (_: Trace) (_: Mem) (_: Locals) => x = x))
      end
  end.

Ltac add_equality_to_post x Post :=
  let y := fresh "etmp0" in
  (* using pose & context match instead of set because set adds the renaming @{x:=y}
     to the evar, so x will not be in the evar scope any more at the end, even though
     x was introduced before the evar was created *)
  pose (y := x);
  lazymatch goal with
  | |- context C[x] => let C' := context C[y] in change C'
  end;
  eapply (ands_cons (eq_refl y : y = x)) in Post;
  clearbody y.

Ltac add_equalities_to_post Post :=
  lazymatch goal with
  (* loop invariant *)
  | |- ?E ?Measure ?T ?M ?L =>
      add_equality_to_post L Post;
      add_equality_to_post T Post;
      add_equality_to_post Measure Post
  (* if branch post *)
  | |- ?E ?T ?M ?L =>
      add_equality_to_post L Post;
      add_equality_to_post T Post
  end.

Ltac add_var_to_post x Post :=
  first
    [ let rhs := eval cbv delta [x] in x in
      (tryif is_var rhs then idtac else (
        vpattern x in Post;
        lazymatch type of Post with
        | ?f x => change (dlet x f) in Post
        end));
      subst x
    | vpattern x in Post;
      eapply ex_intro in Post;
      clear x ].

Ltac add_last_var_to_post Post :=
  let lastvar :=
    match goal with
    | x: _ |- _ =>
        let __ := match constr:(Set) with
                  | _ => assert_fails (constr_eq x Post)
                  end in x
    end in
  let T := type of lastvar in
  lazymatch T with
  | scope_marker _ => fail "done (scope marker reached)"
  | _ => idtac
  end;
  lazymatch type of T with
  | Prop => clear lastvar
  | _ => lazymatch goal with
         (* at the beginning of a while loop, where we have to instantiate the
            loop invariant, the goal is of form (?invariant measure_tmp t_tmp m_tmp l_tmp *)
         | |- _ lastvar _ _ _ => move lastvar at top
         (* after an if branch, the goal is of form (?post t_tmp m_tmp l_tmp) *)
         | |- _ lastvar _ _ => move lastvar at top
         | |- _ _ lastvar _ => move lastvar at top
         | |- _ _ _ lastvar => move lastvar at top
         (* if lastvar is not a _tmp var to be patterned out later, add it to post: *)
         | |- _ => add_var_to_post lastvar Post
         end
  end.

Ltac fold_seps P :=
  lazymatch P with
  | sep ?hd ?tl => let r := fold_seps tl in constr:(cons hd r)
  | _ => constr:(cons P nil)
  end.

Ltac fold_seps_in_hyp H :=
  lazymatch type of H with
  | ?P ?m => let l := fold_seps P in change (seps l m) in H
  end.

Ltac package_context :=
  lazymatch goal with
  | H: _ ?m |- ?E ?t ?m ?l =>
      (* always package sep log assertion, even if memory was not changed in current block *)
      move H at bottom;
      fold_seps_in_hyp H
  | |- ?E ?t ?m ?l => fail "No separation logic hypothesis about" m "found"
  end;
  let Post := fresh "Post" in
  eassert _ as Post by (repeat add_last_hyp_to_post; apply ands_nil);
  add_equalities_to_post Post;
  repeat add_last_var_to_post Post;
  lazymatch goal with
  | |- _ ?Measure ?T ?M ?L => pattern Measure, T, M, L in Post
  | |- _ ?T ?M ?L => pattern T, M, L in Post
  end;
  exact Post.

Section MergingAnd.
  Lemma if_dlet_l_inline: forall (b: bool) (T: Type) (rhs: T) (body: T -> Prop) (P: Prop),
      (if b then dlet rhs body else P) ->
      (if b then body rhs else P).
  Proof. unfold dlet. intros. assumption. Qed.

  Lemma if_dlet_r_inline: forall (b: bool) (T: Type) (rhs: T) (body: T -> Prop) (P: Prop),
      (if b then P else dlet rhs body) ->
      (if b then P else body rhs).
  Proof. unfold dlet. intros. assumption. Qed.

  Lemma pull_if_exists_l (b: bool) (T: Type) {inh: inhabited T} (body: T -> Prop) (P: Prop):
      (if b then (exists x, body x) else P) ->
      exists x, if b then body x else P.
  Proof. intros. destruct b; fwd; [exists x|exists default]; assumption. Qed.

  Lemma pull_if_exists_r (b: bool) (T: Type) {inh: inhabited T} (body: T -> Prop) (P: Prop):
      (if b then P else (exists x, body x)) ->
      exists x, if b then P else body x.
  Proof. intros. destruct b; fwd; [exists default|exists x]; assumption. Qed.

  Lemma if_ands_same_head: forall (b: bool) (P: Prop) (Qs1 Qs2: list Prop),
      (if b then ands (P :: Qs1) else ands (P :: Qs2)) ->
      P /\ (if b then ands Qs1 else ands Qs2).
  Proof. cbn. intros. destruct b; intuition idtac. Qed.

  Local Set Warnings "-notation-overridden".
  Local Infix "++" := SeparationLogic.app. Local Infix "++" := app : list_scope.
  Let nth n xs := SeparationLogic.hd True (SeparationLogic.skipn n xs).
  Let remove_nth n (xs : list Prop) :=
    (SeparationLogic.firstn n xs ++ SeparationLogic.tl (SeparationLogic.skipn n xs)).

  Lemma ands_app: forall Ps Qs, ands (Ps ++ Qs) = (ands Ps /\ ands Qs).
  Proof.
    induction Ps; cbn; intros; apply PropExtensionality.propositional_extensionality;
      rewrite ?IHPs; intuition idtac.
  Qed.

  Lemma ands_nth_to_head: forall (n: nat) (Ps: list Prop),
      (nth n Ps /\ ands (remove_nth n Ps)) = (ands Ps).
  Proof.
    intros. cbv [nth remove_nth].
    pose proof (List.firstn_skipn n Ps: (firstn n Ps ++ skipn n Ps) = Ps).
    forget (skipn n Ps) as Psr.
    forget (firstn n Ps) as Psl.
    subst Ps.
    apply PropExtensionality.propositional_extensionality.
    destruct Psr.
    { cbn. rewrite List.app_nil_r. intuition idtac. }
    cbn [hd tl]. rewrite ?ands_app. cbn [ands]. intuition idtac.
  Qed.

  Lemma merge_ands_at_indices: forall i j (P1 P2: Prop) (b: bool) (Ps1 Ps2: list Prop),
      nth i Ps1 = P1 ->
      nth j Ps2 = P2 ->
      (if b then ands Ps1 else ands Ps2) ->
      (if b then P1 else P2) /\
      (if b then ands (remove_nth i Ps1) else ands (remove_nth j Ps2)).
  Proof.
    intros. subst.
    rewrite <- (ands_nth_to_head i Ps1) in H1.
    rewrite <- (ands_nth_to_head j Ps2) in H1.
    destruct b; intuition idtac.
  Qed.

  Lemma merge_ands_at_indices_same_lhs:
    forall i j {T: Type} (lhs rhs1 rhs2: T) (b: bool) (Ps1 Ps2: list Prop),
      nth i Ps1 = (lhs = rhs1) ->
      nth j Ps2 = (lhs = rhs2) ->
      (if b then ands Ps1 else ands Ps2) ->
      lhs = (if b then rhs1 else rhs2) /\
      (if b then ands (remove_nth i Ps1) else ands (remove_nth j Ps2)).
  Proof.
    intros. eapply merge_ands_at_indices in H1; [ | eassumption.. ].
    destruct b; assumption.
  Qed.

  Lemma merge_ands_at_indices_same_prop: forall i j (P: Prop) (b: bool) (Ps1 Ps2: list Prop),
      nth i Ps1 = P ->
      nth j Ps2 = P ->
      (if b then ands Ps1 else ands Ps2) ->
      P /\ (if b then ands (remove_nth i Ps1) else ands (remove_nth j Ps2)).
  Proof.
    intros. eapply merge_ands_at_indices in H1; [ | eassumption.. ].
    destruct b; assumption.
  Qed.

  Lemma merge_ands_at_indices_neg_prop: forall i j (P: Prop) (b: bool) (Ps1 Ps2: list Prop),
      nth i Ps1 = P ->
      nth j Ps2 = (~P) ->
      (if b then ands Ps1 else ands Ps2) ->
      (if b then P else ~P) /\
        (if b then ands (remove_nth i Ps1) else ands (remove_nth j Ps2)).
  Proof.
    intros. eapply merge_ands_at_indices in H1; eassumption.
  Qed.

  Lemma merge_ands_at_indices_same_mem:
    forall i j (mem: Type) (m: mem) (P1 P2: mem -> Prop) (b: bool) (Ps1 Ps2: list Prop),
      nth i Ps1 = P1 m ->
      nth j Ps2 = P2 m ->
      (if b then ands Ps1 else ands Ps2) ->
      (if b then P1 m else P2 m) /\
        (if b then ands (remove_nth i Ps1) else ands (remove_nth j Ps2)).
  Proof.
    intros. eapply merge_ands_at_indices in H1; [ | eassumption.. ].
    destruct b; assumption.
  Qed.

  Lemma merge_ands_at_indices_seps_same_mem:
    forall i j [word: Type] [mem: map.map word byte]
           (m: mem) (l1 l2: list (mem -> Prop)) (b: bool) (Ps1 Ps2: list Prop),
      nth i Ps1 = seps l1 m ->
      nth j Ps2 = seps l2 m ->
      (if b then ands Ps1 else ands Ps2) ->
      seps (cons (seps (if b then l1 else l2)) nil) m /\
        if b then ands (remove_nth i Ps1) else ands (remove_nth j Ps2).
  Proof.
    intros. eapply merge_ands_at_indices in H1; [ | eassumption.. ].
    destruct b; assumption.
  Qed.
End MergingAnd.

Section MergingSep.

  Local Set Warnings "-notation-overridden".
  Local Infix "++" := SeparationLogic.app. Local Infix "++" := app : list_scope.
  Let nth(n: nat)(xs: list (mem -> Prop)) :=
        SeparationLogic.hd (emp True) (SeparationLogic.skipn n xs).
  Let remove_nth(n: nat)(xs: list (mem -> Prop)) :=
    (SeparationLogic.firstn n xs ++ SeparationLogic.tl (SeparationLogic.skipn n xs)).

  Lemma merge_seps_at_indices (m: mem) (i j: nat)
        (P1 P2: mem -> Prop) (Ps1 Ps2 Qs: list (mem -> Prop)) (b: bool):
    nth i Ps1 = P1 ->
    nth j Ps2 = P2 ->
    seps ((seps (if b then Ps1 else Ps2)) :: Qs) m ->
    seps ((seps (if b then (remove_nth i Ps1) else (remove_nth j Ps2))) ::
          (if b then P1 else P2) :: Qs) m.
  Proof.
    intros. subst. eapply seps'_iff1_seps in H1. eapply seps'_iff1_seps.
    cbn [seps'] in *. unfold remove_nth, nth. destruct b.
    - pose proof (seps_nth_to_head i Ps1) as A.
      eapply iff1ToEq in A. rewrite <- A in H1. ecancel_assumption.
    - pose proof (seps_nth_to_head j Ps2) as A.
      eapply iff1ToEq in A. rewrite <- A in H1. ecancel_assumption.
  Qed.

  (* Note: if the two predicates are at the same address, but have different footprints,
     you might not want to merge them, but first combine them with other sep clauses
     until they both have the same footprint *)
  Lemma merge_seps_at_indices_same_addr_and_pred (m: mem) i j [V: Type] a (v1 v2: V)
        (pred: V -> Z -> mem -> Prop) (Ps1 Ps2 Qs: list (mem -> Prop)) (b: bool):
    nth i Ps1 = pred v1 a ->
    nth j Ps2 = pred v2 a ->
    seps ((seps (if b then Ps1 else Ps2)) :: Qs) m ->
    seps ((seps (if b then (remove_nth i Ps1) else (remove_nth j Ps2)))
            :: pred (if b then v1 else v2) a :: Qs) m.
  Proof.
    intros. eapply (merge_seps_at_indices m i j) in H1; [ | eassumption.. ].
    destruct b; assumption.
  Qed.

  Lemma merge_seps_at_indices_same (m: mem) i j
        (P: mem -> Prop) (Ps1 Ps2 Qs: list (mem -> Prop)) (b: bool):
    nth i Ps1 = P ->
    nth j Ps2 = P ->
    seps ((seps (if b then Ps1 else Ps2)) :: Qs) m ->
    seps ((seps (if b then (remove_nth i Ps1) else (remove_nth j Ps2))) :: P :: Qs) m.
  Proof.
    intros. eapply (merge_seps_at_indices m i j P P) in H1; [ | eassumption.. ].
    destruct b; assumption.
  Qed.

  Lemma merge_seps_done (m: mem) (Qs: list (mem -> Prop)) (b: bool):
    seps ((seps (if b then nil else nil)) :: Qs) m ->
    seps Qs m.
  Proof.
    intros.
    pose proof (seps'_iff1_seps (seps (if b then nil else nil) :: Qs)) as A.
    eapply iff1ToEq in A.
    rewrite <- A in H. cbn [seps'] in H. clear A.
    pose proof (seps'_iff1_seps Qs) as A.
    eapply iff1ToEq in A.
    rewrite A in H. clear A.
    destruct b; cbn [seps] in H; eapply (proj1 (sep_emp_True_l _ _)) in H; exact H.
  Qed.

  Lemma expose_addr_of_then_in_else:
    forall (m: mem) (a: Z) v (Ps1 Ps2 Rs Qs: list (mem -> Prop)) (b: bool),
    impl1 (seps Ps2) (seps ((v a) :: Rs)) ->
    seps ((seps (if b then Ps1 else Ps2)) :: Qs) m ->
    seps ((seps (if b then Ps1 else ((v a) :: Rs))) :: Qs) m.
  Proof.
    intros. destruct b.
    - assumption.
    - (* TODO make seprewrite_in work for impl1 *)
      pose proof (seps'_iff1_seps (seps Ps2 :: Qs)) as A. eapply iff1ToEq in A.
      rewrite <- A in H0. cbn [seps'] in H0. clear A.
      pose proof (seps'_iff1_seps (seps ((v a) :: Rs) :: Qs)) as A. eapply iff1ToEq in A.
      rewrite <- A. cbn [seps']. clear A.
      eassert (impl1 (sep (seps Ps2) (seps' Qs)) (sep (seps (v a :: Rs)) _)) as A. {
        ecancel.
      }
      eapply A. assumption.
  Qed.

End MergingSep.

Lemma push_if_into_arg{A B: Type}(f: A -> B)(a1 a2: A)(cond: bool):
  (if cond then f a1 else f a2) = f (if cond then a1 else a2).
Proof. destruct cond; reflexivity. Qed.

Lemma push_if_into_cons_tuple_same_key(cond: bool)(k: string)(v1 v2: Z) t1 t2:
  (if cond then cons (k, v1) t1 else cons (k, v2) t2)
  = cons (k, if cond then v1 else v2) (if cond then t1 else t2).
Proof. destruct cond; reflexivity. Qed.

Lemma if_same{A: Type}(cond: bool)(a: A): (if cond then a else a) = a.
Proof. destruct cond; reflexivity. Qed.

Ltac is_fresh x := assert_succeeds (pose proof tt as x).

Ltac make_fresh x :=
  tryif is_fresh x then idtac else let x' := fresh x "_0" in rename x into x'.

Ltac letbind_locals start_index :=
  lazymatch goal with
  | |- wp_cmd _ _ _ _ (map.of_list ?kvs) _ =>
      lazymatch eval hnf in (List.nth_error kvs start_index) with
      | None => idtac (* done *)
      | Some (?name, ?val) =>
          tryif is_var val then
            letbind_locals (S start_index)
          else (
            let tmp := fresh in
            set (tmp := val);
            let namei := string_to_ident name in
            make_fresh namei;
            rename tmp into namei;
            letbind_locals (S start_index)
         )
      end
  end.

Ltac pull_dlet_and_exists_step :=
  lazymatch goal with
  | H: if _ then dlet _ (fun x => _) else _ |- _ =>
      make_fresh x;
      lazymatch type of H with
      | if ?c then dlet ?rhs ?body else ?els =>
          pose (x := rhs);
          change (if c then dlet x body else els) in H;
          eapply if_dlet_l_inline in H
      end
  | H: if _ then _ else dlet _ (fun x => _) |- _ =>
      make_fresh x;
      lazymatch type of H with
      | if ?c then ?thn else dlet ?rhs ?body =>
          pose (x := rhs);
          change (if c then thn else dlet x body) in H;
          eapply if_dlet_r_inline in H
      end
  | H: if ?b then (exists x, _) else ?P |- _ =>
      eapply (pull_if_exists_l b _ _ P) in H;
      make_fresh x;
      destruct H as [x H]
  | H: if ?b then ?P else (exists x, _) |- _ =>
      eapply (pull_if_exists_r b _ _ P) in H;
      make_fresh x;
      destruct H as [x H]
  end.

Ltac merge_pair H Ps Qs is_match lem := once (
  lazymatch index_and_element_of Ps with
  | (?i, ?P) =>
      lazymatch find_in_list ltac:(fun Q => is_match P Q) Qs with
      | (?j, ?Q) =>
          eapply (lem i j) in H;
          [ cbn [app firstn tl skipn] in H
          | cbn [hd skipn]; reflexivity .. ]
      end
  end).

Ltac merge_and_pair is_match lem :=
  lazymatch goal with
  | H: if _ then ands ?Ps else ands ?Qs |- _ =>
      merge_pair H Ps Qs is_match lem; destruct H
  end.

Ltac same_lhs P Q :=
  lazymatch P with
  | ?lhs = _ =>
      lazymatch Q with
      | lhs = _ => constr:(true)
      | _ = _ => constr:(false)
      end
  end.

Ltac same_addr_and_pred P Q :=
  lazymatch P with
  | ?pred ?valueP ?addr =>
      lazymatch Q with
      | pred ?valueQ addr => constr:(true)
      | _ => constr:(false)
      end
  | _ => constr:(false)
  end.

Ltac neg_prop P Q :=
  lazymatch Q with
  | ~ P => constr:(true)
  | _ => constr:(false)
  end.

Ltac seps_about_same_mem x y :=
  lazymatch x with
  | seps _ ?m => lazymatch y with
                 | seps _ ?m => constr:(true)
                 | _ => constr:(false)
                 end
  | _ => constr:(false)
  end.

Ltac constr_eqb x y :=
  lazymatch x with
  | y => constr:(true)
  | _ => constr:(false)
  end.

Ltac merge_sep_pair_step :=
  lazymatch goal with
  | H: seps ((seps (if ?b then ?Ps else ?Qs)) :: ?Rs) ?m |- _ =>
      merge_pair H Ps Qs constr_eqb (merge_seps_at_indices_same m) ||
      merge_pair H Ps Qs same_addr_and_pred (merge_seps_at_indices_same_addr_and_pred m) ||
      (eapply merge_seps_done in H; cbn [seps] in H)
  end.

Ltac after_if :=
  repeat match goal with
         | H: sep _ _ ?M |- _ => clear M H
         end;
  intros ? ? ? ?;
  repeat pull_dlet_and_exists_step;
  repeat merge_and_pair constr_eqb merge_ands_at_indices_same_prop;
  repeat merge_and_pair neg_prop merge_ands_at_indices_neg_prop;
  repeat merge_and_pair same_lhs merge_ands_at_indices_same_lhs;
  repeat merge_and_pair seps_about_same_mem merge_ands_at_indices_seps_same_mem;
  repeat merge_sep_pair_step;
  repeat match goal with
  | H: if ?b then ?thn else ?els |- _ =>
      clear H;
      assert_succeeds ( (* test if clearing H was justified because it's redundant: *)
        idtac;
        let sp := constr:(_: BoolSpec _ _ b) in
        lazymatch type of sp with
        | BoolSpec ?Pt ?Pf _ =>
            assert ((Pt -> thn) /\ (Pf -> els)) by (unfold ands; clear; intuition auto)
        end)
    end;
  lazymatch goal with
  | H: ?l = _ |- wp_cmd _ _ _ _ ?l _ =>
      repeat (rewrite ?push_if_into_arg,
                      ?push_if_into_cons_tuple_same_key,
                      ?if_same in H);
      subst l
  end;
  letbind_locals 0%nat.

Inductive snippet :=
| SAssign(is_decl: bool)(x: string)(e: Syntax.expr)
| SStore(sz: access_size)(addr val: Syntax.expr)
| SIf(cond: Syntax.expr)
| SElse
| SWhile(cond: Syntax.expr){Measure: Type}(measure0: Measure)
| SStart
| SEnd
| SRet(xs: list string)
| SEmpty.

Ltac clear_until_LoopInvariant_marker :=
  repeat match goal with
         | x: ?T |- _ => lazymatch T with
                         | scope_marker LoopInvariant => fail 1
                         | _ => clear x
                         end
         end;
  match goal with
  | x: ?T |- _ => lazymatch T with
                  | scope_marker LoopInvariant => clear x
                  end
  end.

Ltac expect_and_clear_last_marker expected :=
  lazymatch goal with
  | H: scope_marker ?sk |- _ =>
      tryif constr_eq sk expected then
        clear H
      else
        fail "Assertion failure: Expected last marker to be" expected "but got" sk
  end.

Ltac destruct_ifs :=
  repeat match goal with
         | H: context[if ?b then _ else _] |- _ =>
             let t := type of b in constr_eq t bool; destr b
         | |- context[if ?b then _ else _] =>
             let t := type of b in constr_eq t bool; destr b
         end.

Ltac ZWords := unfold wwrap, wswrap in *; better_lia.

Ltac prove_concrete_post_pre :=
    repeat match goal with
           | H: List.length ?l = S _ |- _ =>
               is_var l; destruct l;
               [ discriminate H
               | cbn [List.length] in H; eapply Nat.succ_inj in H ]
           | H: List.length ?l = O |- _ =>
               is_var l; destruct l;
               [ clear H
               | discriminate H ]
           end;
    repeat match goal with
           | x := _ |- _ => subst x
           end;
    rewrite ?Z.min_to_leb_dec, ?Z.max_to_leb_dec in *; (* <-- TODO make less ad-hoc *)
    destruct_ifs;
    repeat match goal with
           | H: ands (_ :: _) |- _ => destruct H
           | H: ands nil |- _ => clear H
           end;
    cbn [List.app List.firstn List.nth] in *;
    repeat match goal with
           | |- exists _, _ => eexists
           | |- _ /\ _ => split
           | |- ?x = ?x => reflexivity
           | |- sep _ _ _ => ecancel_assumption
           | H: _ \/ _ |- _ => destruct H (* <-- might become expensive... *)
           end;
    try lia.

Ltac prove_concrete_post := prove_concrete_post_pre; egg_simpl_or_prove.

Ltac ret retnames :=
  lazymatch goal with
  | B: scope_marker ?sk |- _ =>
      lazymatch sk with
      | FunctionBody => idtac
      | ThenBranch => fail "return inside a then-branch is not supported"
      | ElseBranch => fail "return inside an else-branch is not supported"
      | LoopBody => fail "return inside a loop body is not supported"
      end
  | |- _ => fail "block structure lost (could not find a scope_marker)"
  end;
  eapply wp_skip;
  lazymatch goal with
  | |- exists _, map.getmany_of_list _ ?eretnames = Some _ /\ _ =>
    unify eretnames retnames
  end;
  eexists; split; [reflexivity| ].

Ltac close_block :=
  lazymatch goal with
  | B: scope_marker ?sk |- _ =>
      lazymatch sk with
      | ElseBranch =>
          eapply wp_skip;
          package_context
      | LoopBody =>
          eapply wp_skip;
          prove_concrete_post
      | FunctionBody =>
          lazymatch goal with
          | |- @ready ?g => change g
          | |- _ => idtac
          end;
          lazymatch goal with
          | |- wp_cmd _ _ _ _ _ _ => ret (@nil string)
          | |- _ => idtac (* ret nonEmptyVarList was already called *)
          end;
          prove_concrete_post
      | _ => fail "Can't end a block here"
      end
  | _ => fail "no scope marker found"
  end.

Ltac prettify_goal :=
  lazymatch goal with
  | |- _ =>
      cbv beta in *;
      after_if
  end.

Ltac add_snippet s :=
  assert_no_error;
  lazymatch s with
  | SAssign ?is_decl ?name ?val => eapply (wp_set _ name val) (* TODO validate is_decl *)
  | SStore ?sz ?addr ?val => eapply (wp_store _ sz addr val)
  | SIf ?c => eapply (wp_if_bool_dexpr _ c); pose proof mk_temp_if_marker
  | SElse =>
      assert_scope_kind ThenBranch;
      eapply wp_skip;
      package_context
  | SWhile ?cond ?measure0 =>
      eapply (wp_while measure0 cond);
      [ package_context
      | eauto with wf_of_type
      | repeat match goal with
          | H: sep _ _ ?M |- _ => clear M H
          end;
        clear_until_LoopInvariant_marker;
        cbv beta iota delta [ands];
        cbn [seps] in *;
        (* Note: will also appear after loop, where we'll have to clear it,
           but we have to pose it here because the foralls are shared between
           loop body and after the loop *)
        (let n := fresh "Scope0" in pose proof (mk_scope_marker LoopBody) as n);
        intros;
        fwd;
        lazymatch goal with
        | |- exists b, dexpr_bool3 _ _ _ b _ _ _ => eexists
        | |- _ => fail "assertion failure: hypothesis of wp_while has unexpected shape"
        end ]
  | SStart => start
  | SEnd => close_block
  | SRet ?retnames => ret retnames
  | SEmpty => prettify_goal
  end.

Ltac lia' := purify; lia.

Ltac step :=
  lazymatch goal with
  | |- dexpr_bool3 _ _ (expr.lazy_and _ _)       _ _ _ _ => eapply dexpr_lazy_and
  | |- dexpr_bool3 _ _ (expr.lazy_or _ _)        _ _ _ _ => eapply dexpr_lazy_or
  | |- dexpr_bool3 _ _ (expr.not _)              _ _ _ _ => eapply dexpr_not
  | |- dexpr_bool3 _ _ (expr.op bopname.eq _ _)  _ _ _ _ => eapply dexpr_eq
  | |- dexpr_bool3 _ _ (expr.op bopname.ltu _ _) _ _ _ _ => eapply dexpr_ltu
(*| |- dexpr_bool3 _ _ _ _ => eapply mk_dexpr_bool_prop (* fallback *)*)
  | |- dexpr1 _ _ (expr.var _)     _ _ => eapply dexpr1_var; [reflexivity|lia'| ]
  | |- dexpr1 _ _ (expr.literal _) _ _ => eapply dexpr1_literal; [lia'| ]
  | |- dexpr1 _ _ (expr.op _ _ _)  _ _ => eapply dexpr1_binop_unf
  | |- dexpr1 _ _ (expr.load _ _)  _ _ => eapply dexpr1_load
  | |- bool_expr_branches _ _ _ _ => eapply BoolSpec_expr_branches; [ intro | intro | ]
  | |- save_mem_hyp _ ?m =>
      lazymatch goal with
      | H: sep _ _ m |- _ => exact H
      end
  | |- new_mem_hyp ?P ?m -> ?Q =>
      lazymatch goal with
      | H: sep _ _ m |- _ => clear H; change (P m -> Q); intro
      end
  | |- with_new_mem _ _ _ _ _ _ =>
      lazymatch goal with
      | H: sep _ _ ?m |- _ => clear H m; intros ? ?
      end
  | |- then_branch_marker ?G =>
      let H := lazymatch goal with H: temp_if_marker |- _ => H end in
      let n := fresh "Scope0" in
      pose proof (mk_scope_marker ThenBranch) as n;
      move n before H;
      clear H;
      change G
  | |- else_branch_marker ?G =>
      let H := lazymatch goal with H: temp_if_marker |- _ => H end in
      let n := fresh "Scope0" in
      pose proof (mk_scope_marker ElseBranch) as n;
      move n before H;
      clear H;
      change G
  | |- after_if ?fs ?b ?Q1 ?Q2 ?rest ?post =>
      lazymatch goal with
      | H: temp_if_marker |- _ => clear H
      end;
      tryif is_evar Q1 then idtac (* need to first complete then-branch *)
      else tryif is_evar Q2 then idtac (* need to first complete else-branch *)
      else after_if
  | |- True => constructor
  | |- wp_cmd _ _ _ _ (map.put ?l ?x ?v) _ => put_into_current_locals
  | |- wp_cmd _ _ _ _ _ _ =>
      lazymatch goal with
      | |- ?G => change (@ready G)
      end
  | |- sep _ _ _ /\ _ =>
      lazymatch goal with
      | |- ?G => change (@pre_canceling G)
      end
  | |- pre_canceling _ => pre_cancel_step
  | |- pre_canceling_done ?G =>
      lazymatch G with
      | _ /\ _ => split
      | _ => idtac
      end;
      [ use_sep_assumption; reify_goal | .. ]
  | |- holds _ _ =>
      unfold holds in *; use_sep_assumption; reify_goal
  | |- iff1 (seps ?LHS) (seps ?RHS) =>
      first
        [ constr_eq LHS RHS; exact (iff1_refl _)
        | cancel_step
        | cancel_emp_l
        | cancel_emp_r
        | lazymatch goal with
          | |- iff1 (seps (cons ?x nil)) _ => is_evar x
          | |- iff1 _ (seps (cons ?x nil)) => is_evar x
          end;
          cbn [seps];
          exact (iff1_refl _) ]
  end.

(* fail on notations that we don't want to destruct *)
Ltac is_destructible_and T ::=
  lazymatch T with
  | (Logic.and (N.le     _ ?y) (N.le     ?y _)) => fail
  | (Logic.and (Z.le     _ ?y) (Z.le     ?y _)) => fail
  | (Logic.and (Peano.le _ ?y) (Peano.le ?y _)) => fail
  | (Logic.and (Pos.le   _ ?y) (Pos.le   ?y _)) => fail
  | (Logic.and (N.le     _ ?y) (N.lt     ?y _)) => fail
  | (Logic.and (Z.le     _ ?y) (Z.lt     ?y _)) => fail
  | (Logic.and (Peano.le _ ?y) (Peano.lt ?y _)) => fail
  | (Logic.and (Pos.le   _ ?y) (Pos.lt   ?y _)) => fail
  | (Logic.and (N.lt     _ ?y) (N.le     ?y _)) => fail
  | (Logic.and (Z.lt     _ ?y) (Z.le     ?y _)) => fail
  | (Logic.and (Peano.lt _ ?y) (Peano.le ?y _)) => fail
  | (Logic.and (Pos.lt   _ ?y) (Pos.le   ?y _)) => fail
  | (Logic.and (N.lt     _ ?y) (N.lt     ?y _)) => fail
  | (Logic.and (Z.lt     _ ?y) (Z.lt     ?y _)) => fail
  | (Logic.and (Peano.lt _ ?y) (Peano.lt ?y _)) => fail
  | (Logic.and (Pos.lt   _ ?y) (Pos.lt   ?y _)) => fail
  | (Logic.and head_of_implicit_facts _) => fail
  | (Logic.and _ _) => idtac
  end.

(* If t1 solves the first goal, t2 will be run on the second (now first) goal,
   so t2 can do operations that only became possible because of t1's evar instantiations.
   Requires `Set Default Goal Selector "all".` *)
Ltac run2on1stGoal :=
  ltac2:(t1 t2 |- Control.focus 1 1 (fun _ => (Ltac1.run t1));
                  Control.focus 1 1 (fun _ => (Ltac1.run t2))).

(*
Set Default Goal Selector "all".

Ltac t :=
  lazymatch goal with
  | |- ?G => idtac G
  end.

Goal forall (a b: nat), a = b -> a = b /\ b = a /\ (a + b = b + a)%nat.
Proof.
  intros. repeat split.
  run2on1stGoal ltac:(idtac; t; try assumption) ltac:(idtac; t; symmetry).
*)

Ltac step_is_done :=
  match goal with
  | |- @ready _ => idtac
  | |- after_if _ _ ?Q1 ?Q2 _ _ => is_evar Q1
  | |- after_if _ _ ?Q1 ?Q2 _ _ => is_evar Q2
  end.

Ltac run_steps :=
  tryif step_is_done then idtac
  else tryif step then run_steps
  else pose_err Error:("'step' should not fail here").

(* can be overridden with idtac for debugging *)
Ltac run_steps_hook := run_steps.

(*
  intros;
  fwd;
  (* leftover from word_simpl_step_in_hyps, TODO where to put? in fwd? *)
  repeat match goal with
         | H: ?x = ?y |- _ => is_var x; is_var y; subst x
         end.
*)

(* Note: An rhs_var appears in expressions and, in our setting, always has a corresponding
   var (of type word) bound in the current context, whereas an lhs_var may or may not be
   bound in the current context, if not bound, a new entry will be added to current_locals. *)

Declare Custom Entry rhs_var.
Notation "x" :=
  (match x with
   | _ => ltac2:(exact_varconstr_as_string (Ltac2.Constr.pretype x))
   end)
  (in custom rhs_var at level 0, x constr at level 0, only parsing).

Declare Custom Entry var_or_literal.
Notation "x" :=
  (match x with
   | _ => ltac:(lazymatch isZcst x with
                | true => refine (expr.literal _); exact x
                | false => refine (expr.var _); exact_varconstr_as_string x
                end)
   end)
  (in custom var_or_literal at level 0, x constr at level 0, only parsing).

Declare Custom Entry lhs_var.
Notation "x" := (ident_to_string x)
  (in custom lhs_var at level 0, x constr at level 0, only parsing).

Declare Custom Entry rhs_var_list.
Notation "x" := (cons x nil)
  (in custom rhs_var_list at level 0, x custom rhs_var at level 0, only parsing).
Notation "h , t" := (cons h t)
  (in custom rhs_var_list at level 0,
   h custom rhs_var at level 0,
   t custom rhs_var_list at level 0,
   only parsing).

Declare Custom Entry live_expr.

Notation "x" := x
  (in custom live_expr at level 0, x custom var_or_literal at level 0, only parsing).

Notation "live_expr:( e )" := e
  (e custom live_expr at level 100, only parsing).

Notation "( e )" := e (in custom live_expr, e custom live_expr at level 100).

(* Using the same precedences as https://en.cppreference.com/w/c/language/operator_precedence *)
Notation "! x" := (expr.not x)
  (in custom live_expr at level 2, x custom live_expr, right associativity, only parsing).
Infix "*" := (expr.op bopname.mul)
  (in custom live_expr at level 3, left associativity, only parsing).
Infix "/" := (expr.op bopname.divu)
  (in custom live_expr at level 3, left associativity, only parsing).
Infix "%" := (expr.op bopname.remu)
  (in custom live_expr at level 3, left associativity, only parsing).
Infix "+" := (expr.op bopname.add)
  (in custom live_expr at level 4, left associativity, only parsing).
Infix "-" := (expr.op bopname.sub)
  (in custom live_expr at level 4, left associativity, only parsing).
Infix "<<" := (expr.op bopname.slu)
  (in custom live_expr at level 5, left associativity, only parsing).
Infix ">>" := (expr.op bopname.sru)
  (in custom live_expr at level 5, left associativity, only parsing).
Infix "<" := (expr.op bopname.ltu)
  (in custom live_expr at level 6, no associativity, only parsing).
Notation "a <= b" := (expr.not (expr.op bopname.ltu b a))
  (in custom live_expr at level 6, a custom live_expr, b custom live_expr,
   no associativity, only parsing).
Notation "a > b" := (expr.op bopname.ltu b a)
  (in custom live_expr at level 6, a custom live_expr, b custom live_expr,
   no associativity, only parsing).
Notation "a >= b" := (expr.not (expr.op bopname.ltu a b))
  (in custom live_expr at level 6, a custom live_expr, b custom live_expr,
   no associativity, only parsing).
Infix "==" := (expr.op bopname.eq)
  (in custom live_expr at level 7, no associativity, only parsing).
Infix "&" := (expr.op bopname.and)
  (in custom live_expr at level 8, left associativity, only parsing).
Infix "^" := (expr.op bopname.xor)
  (in custom live_expr at level 9, left associativity, only parsing).
Infix "|" := (expr.op bopname.or)
  (in custom live_expr at level 10, left associativity, only parsing).
Infix "&&" := expr.lazy_and
  (in custom live_expr at level 11, left associativity, only parsing).
Infix "||" := expr.lazy_or
  (in custom live_expr at level 12, left associativity, only parsing).
Notation "c ? e1 : e2" := (expr.ite c e1 e2)
  (in custom live_expr at level 13, right associativity, only parsing).

Notation "load1( a )" := (expr.load access_size.one a)
  (in custom live_expr at level 0, a custom live_expr at level 100, only parsing).
Notation "load2( a )" := (expr.load access_size.two a)
  (in custom live_expr at level 0, a custom live_expr at level 100, only parsing).
Notation "load4( a )" := (expr.load access_size.four a)
  (in custom live_expr at level 0, a custom live_expr at level 100, only parsing).
Notation  "load( a )" := (expr.load access_size.word a)
  (in custom live_expr at level 0, a custom live_expr at level 100, only parsing).

Goal forall (word: Type) (x: word),
    live_expr:(x + 3) = expr.op bopname.add (expr.var "x") (expr.literal 3).
Proof. intros. reflexivity. Abort.

Goal forall (word: Type) (x: word),
  live_expr:(x <= 3) =
  expr.op bopname.eq (expr.op bopname.ltu (expr.literal 3) (expr.var "x")) (expr.literal 0).
Proof. intros. reflexivity. Abort.

Declare Custom Entry snippet.

Notation "*/ s /*" := s (s custom snippet at level 100).
Notation "*/ /*" := SEmpty.
Notation "x = e ;" := (SAssign false x e) (* rhs as in "already declared" (but still on lhs) *)
  (in custom snippet at level 0, x custom rhs_var at level 100, e custom live_expr at level 100).
Notation "'uintptr_t' x = e ;" := (SAssign true x e)
  (in custom snippet at level 0, x custom lhs_var at level 100, e custom live_expr at level 100).
Notation "store1( a , v ) ;" := (SStore access_size.one a v)
  (in custom snippet at level 0,
   a custom live_expr at level 100, v custom live_expr at level 100).
Notation "store2( a , v ) ;" := (SStore access_size.two a v)
  (in custom snippet at level 0,
   a custom live_expr at level 100, v custom live_expr at level 100).
Notation "store4( a , v ) ;" := (SStore access_size.four a v)
  (in custom snippet at level 0,
   a custom live_expr at level 100, v custom live_expr at level 100).
Notation "store( a , v ) ;" := (SStore access_size.word a v)
  (in custom snippet at level 0,
   a custom live_expr at level 100, v custom live_expr at level 100).
Notation "'return' l ;" := (SRet l)
  (in custom snippet at level 0, l custom rhs_var_list at level 1).

Notation "'if' ( e ) {" := (SIf e) (in custom snippet at level 0, e custom live_expr).
Notation "{" := SStart (in custom snippet at level 0).
Notation "}" := SEnd (in custom snippet at level 0).
Notation "} 'else' {" := SElse (in custom snippet at level 0).

Notation "'while' ( e ) /* 'decreases' m */ {" :=
  (SWhile e m) (in custom snippet at level 0, e custom live_expr, m constr at level 0).

Set Ltac Backtrace.

(* COQBUG (performance) https://github.com/coq/coq/issues/10743#issuecomment-530673037
   Probably fixed on master *)
Ltac cond_hyp_factor :=
  repeat match goal with
         | H : ?x -> _, H' : ?x -> _ |- _  =>
           pose proof (fun u : x => conj (H u) (H' u)); clear H H'
         end.

(* probably not needed any more in recent versions *)
Ltac adhoc_lia_performance_fixes :=
  repeat match goal with
         | H: ?P -> _ |- _ => assert_succeeds (assert (~ P) by (clear; Lia.lia)); clear H
         end;
  repeat match goal with
         | H: ?P -> _ |- _ => let A := fresh in (assert P as A by (clear; Lia.lia));
                              specialize (H A); clear A
         end;
  cond_hyp_factor;
  subst.

(* If we use dexpr_bool_prop, but want to get derive a provably deterministic spec
   from the Props generated by dexpr_bool_prop, can that work? *)

Local Open Scope Z_scope.

Existing Class Bool.reflect.
Global Existing Instance Z.leb_spec0.
Global Existing Instance BinInt.Z.eqb_spec.

Global Instance reflect_and(P1 P2: Prop)(b1 b2: bool)
  {r1: Bool.reflect P1 b1}{r2: Bool.reflect P2 b2}: Bool.reflect (P1 /\ P2) (b1 && b2).
Proof.
  destruct r1; destruct r2; constructor; intuition auto.
Qed.

(* not as general as it could be, requires reproving all lemmas previously proven
   for regular if
Definition ite(P: Prop){b: bool}{r: Bool.reflect P b}{A: Type}(thn els: A): A :=
  if b then thn else els.
*)

(* P and r are not involved in the computation at all, they are only there to
   help infer b. *)
Definition dec(P: Prop){b: bool}{r: Bool.reflect P b}: bool := b.

Notation "'If' c 'then' a 'else' b" := (if dec c then a else b) (at level 200).

Goal forall (a b c: Z), True.
  intros.
  pose (If a = b then 1 else 2).
  pose (If a <= c then a else c).
  pose (If a <= b <= c then 1 else 0).
Abort.


(* BoolSpec disadvantage: could allow unwanted instances like this one: *)
Goal forall a b: Z, BoolSpec (a < b + 3) (b < a + 3) (a <? b)%Z.
  intros. destr (a <? b)%Z; constructor; lia.
Abort.

(* BoolSpec advantage: allows two different Props, eg for
Z.leb_spec : forall x y : Z, BoolSpec (x <= y) (y < x) (x <=? y)
the false case results in (y < x), which is nicer than (~ x <= y). *)

(* Mutually exclusive BoolSpec
   XBoolSpec P Q b essentially says Bool.reflect P b and Q is a prettier version of ~P
Inductive XBoolSpec (P Q : Prop) : bool -> Prop :=
| XBoolSpecT : P -> ~Q -> XBoolSpec P Q true
| XBoolSpecF : ~P -> Q -> XBoolSpec P Q false.
(* destructing this one leads to both P and ~Q, or both ~P and Q, which is redundant *)
*)

Global Instance andb_BoolSpec(Pt Pf Qt Qf: Prop)(p q: bool)
  {sp: BoolSpec Pt Pf p}{sq: BoolSpec Qt Qf q}: BoolSpec (Pt /\ Qt) (Pf \/ Qf) (p && q).
Proof.
  destruct sp; destruct sq; constructor; intuition auto.
Qed.

Global Instance orb_BoolSpec(Pt Pf Qt Qf: Prop)(p q: bool)
  {sp: BoolSpec Pt Pf p}{sq: BoolSpec Qt Qf q}: BoolSpec (Pt \/ Qt) (Pf /\ Qf) (p || q).
Proof.
  destruct sp; destruct sq; constructor; intuition auto.
Qed.

(* might lead to cyclic typeclass search if the Props are inputs and the bool is an output,
   might need a Hint Extern with an Ltac that checks that p is not an evar *)
Global Instance negb_BoolSpec(Pt Pf: Prop)(p: bool){sp: BoolSpec Pt Pf p}:
  BoolSpec Pt Pf p -> BoolSpec Pf Pt (negb p).
Proof.
  destruct sp; constructor; intuition auto.
Qed.

(*
Class XBoolSpec(P Q: Prop)(b: bool): Prop := {
  boolSpec: BoolSpec P Q b;
  XBoolSpec_exclusive: P <-> ~Q;
}.
*)

(* TODO plan for bools:
   evaluating if/loop conditions returns bool instead of Prop, but the wp_if/wp_loop
   lemmas infer a BoolSpec to use (PTrue -> thenbranchexecution) and
   (PFalse -> elsebranchexecution), and the (if _ then _ else _) expressions use the boolean
   expression (no special Prop-consuming upper-case If), because these ifs should only
   be visible in states not displayed to the user, and in computed postconditions, which,
   at the moment, only need to be deterministic and not depend on too many inputs, but
   not particularly "nice".
   Later maybe add notation dec and If notation:

*)
Module decAlt.
  Class PrettyNegation(P Q: Prop): Prop := {
    prettyNegation_spec: P <-> ~Q;
  }.
  Definition dec(P: Prop){notP: Prop}{_: PrettyNegation P notP}{b: bool}{r: BoolSpec P notP b}: bool := b.
End decAlt.

Require Import coqutil.Sorting.Permutation.

Import Syntax BinInt String List.ListNotations ZArith.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Open Scope bool_scope.

Require Import coqutil.Datatypes.ZList.
Import ZList.List.ZIndexNotations. Local Open Scope zlist_scope.
Require Import coqutil.Word.Bitwidth32.
Open Scope sep_bullets_scope.

(* Note: If you re-import ZnWords after this, you'll get the old better_lia again *)
Ltac better_lia ::=
  Z.div_mod_to_equations;
  adhoc_lia_performance_fixes;
  Lia.lia.

Local Set Default Goal Selector "all".

Tactic Notation ".*" constr(s) "*" :=
  run2on1stGoal ltac:(idtac; add_snippet s; run_steps_hook) ltac:(idtac; run_steps_hook).

Require Import Ltac2.Ltac2.

Ltac2 add_snippet(s: constr) := ltac1:(s |- add_snippet s) (Ltac1.of_constr s).
Ltac2 run_steps_hook () := ltac1:(run_steps_hook).

Ltac2 next_snippet(s: unit -> constr) :=
  match Control.case (fun _ => Control.focus 1 2 (fun _ => ())) with
  | Val _ => (* there are >= 2 open goals *)
      Control.focus 1 1 (fun _ => add_snippet (s ()); run_steps_hook ());
      Control.focus 1 1 run_steps_hook
  | Err _ => (* at most 1 open goal *)
      Control.focus 1 1 (fun _ => add_snippet (s ()); run_steps_hook ())
  end.

Ltac2 Notation ".*" s(thunk(constr)) "*" := next_snippet s.

Ltac2 step () := ltac1:(step).

Ltac2 Notation "step" := step ().

Comments C_STARTS_HERE
/**.

Definition u_min: {f: list string * list string * cmd &
  forall fs t m a b (R: mem -> Prop),
    R m ->
    0 <= a < 2 ^ 32 ->
    0 <= b < 2 ^ 32 ->
    vc_func fs f t m [|a; b|] (fun t' m' retvs =>
      t' = t /\ R m' /\ retvs = [| if a <? b then a else b |]
  )}.                                                                           .**/
{                                                                          /**. (* .**/
  uintptr_t r = 0;                                                         /**. .**/

  if (! (a < b && b < 10)) {                                                   /**.

  if (a < b && b < 10) {                                                   /**.

  match goal with
  | |- bool_expr_branches _ _ _ _ =>
      eapply BoolSpec_expr_branches;
      [ once (typeclasses eauto)
      | .. ]
  end.



.**/
    r = a;                                                                 /**. .**/
  } else {                                                                 /**. .**/
    r = b;                                                                 /**. .**/
  }                                                                        /**. .**/
                                                                           /**. .**/
  return r;                                                                /**. .**/
}                                                                          /**.
Defined.
*)
Abort.

Unset Implicit Arguments.

Require Import FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Set Default Proof Mode "Classic".

Lemma wltu_wf: well_founded (fun x y: Z => wwrap x < wwrap y).
Proof.
  epose proof (well_founded_ltof _ (fun (w: Z) => Z.to_nat (wwrap w))) as P.
  unfold ltof in P.
  eqapply P.
  extensionality a. extensionality b. eapply propositional_extensionality.
  split; ZWords.
Qed.

(* Assigns default well_founded relations to types.
   Use lower costs to override existing entries. *)
Create HintDb wf_of_type.
#[export] Hint Resolve wltu_wf | 4 : wf_of_type.

Section WithNonmaximallyInsertedA.
  Context [A: Type].

  Lemma List__repeat_0: forall (a: A), List.repeat a 0 = nil.
  Proof. intros. reflexivity. Qed.
End WithNonmaximallyInsertedA.

(* ARP responder example *)

Definition MAC := array_t (uint_t 8) 6.
Global Hint Extern 1 (RepPredicate MAC) => exact (array (uint 8) 6) : typeclass_instances.

Definition IPv4 := array_t (uint_t 8) 4.
Global Hint Extern 1 (RepPredicate IPv4) => exact (array (uint 8) 4) : typeclass_instances.

Definition ARPOperationRequest: Z := 1.
Definition ARPOperationReply: Z := 2.

Record ARPPacket_t := mkARPPacket {
  htype: uint_t 16; (* hardware type *)
  ptype: uint_t 16; (* protocol type *)
  hlen: uint_t 8;   (* hardware address length (6 for MAC addresses) *)
  plen: uint_t 8;   (* protocol address length (4 for IPv4 addresses) *)
  oper: uint_t 16;
  sha: MAC;  (* sender hardware address *)
  spa: IPv4; (* sender protocol address *)
  tha: MAC;  (* target hardware address *)
  tpa: IPv4; (* target protocol address *)
}.

Record EthernetHeader_t := mkEthernetHeader {
  dstMAC: MAC;
  srcMAC: MAC;
  etherType: uint_t 16;
}.

(* TODO move to coqutil *)
Global Instance Bool_eqb_spec: EqDecider Bool.eqb.
Proof. intros. destruct x; destruct y; constructor; congruence. Qed.

Global Hint Extern 1 (RepPredicate (uint_t ?nbits)) =>
  exact (uint nbits) : typeclass_instances.

Global Hint Extern 1 (RepPredicate (array_t ?T ?n)) =>
 exact (@array T _ n _ _) : typeclass_instances.

Ltac create_predicate_rec refine_already_introd :=
  lazymatch goal with
  | |- forall (lastField: ?T), Z -> ?mem -> Prop =>
      let f := fresh lastField in
      intro f;
      refine_already_introd;
      match constr:(_ : RepPredicate T) with
      | ?p => exact (p f)
      end
  | |- forall (name: ?T), _ =>
      let f := fresh name in
      intro f;
      match constr:(_ : RepPredicate T) with
      | ?p => create_predicate_rec ltac:(refine_already_introd; refine (sepapp (p f) _))
      end
  end.

Ltac create_predicate :=
  match goal with
  | |- ?G => let t := constr:(ltac:(
                let p := fresh in intro p; case p; create_predicate_rec idtac) : G) in
             let t' := eval cbv beta in t in
             exact t'
  end.

Global Instance ARPPacket: RepPredicate ARPPacket_t :=
  ltac:(create_predicate).

Global Instance EthernetHeader: RepPredicate EthernetHeader_t :=
  ltac:(create_predicate).

(* New Feature TODO:
   Allow "breakpoints" /**. .**/ anywhere inside expressions,
   and allow removing /**. .**/ between statements.

eg
   a + /**. .**/ b
but also
   call1(args1); call2(args2)
*)

(* TODO: min function where both args and res could all be aliased,
   can we do it with several hyps about mem, or with and1?

Pre:  (a @@ pa /\ b @@ pb /\ c @@ pc) * R
Body: *pc = min( *pa, *pb )
Post: (any @@ pa /\ any @@ pb /\ min(a,b) @@ pc) * R
*)

Global Hint Extern 1 (PredicateSize (same_range ?pred) _) =>
         exact (_: PredicateSize pred _) : typeclass_instances.

(* needed if v is of type Z rather than (uint_t ?nbits) *)
Global Hint Extern 2 (PredicateSize (uint ?nbits ?v) _) =>
  lazymatch nbits with
  | 8 => exact (uint_8_PredicateSize v)
  | 16 => exact (uint_16_PredicateSize v)
  | 32 => exact (uint_32_PredicateSize v)
  | 64 => exact (uint_64_PredicateSize v)
  | _ => exact (uint_width_PredicateSize v)
  end
: typeclass_instances.

(* Needed if a and b are of type (uint_t ?nbits) instead of Z *)
#[export] Hint Extern 5 (BoolSpec _ _ (?zOp ?a ?b)) =>
  lazymatch constr:(fun x y: Z => _ : BoolSpec _ _ (zOp x y)) with
  | (fun _ _ => ?s _ _) => exact (s a b)
  end
: typeclass_instances.

(* not a Lemma because this kind of goal will be solved inline by sepcalls canceler *)
Goal forall (bs: list (uint_t 8)) (R: mem -> Prop) a m (Rest: EthernetHeader_t -> Prop),
    sep (array (uint 8) 14 bs a) R m ->
    exists h, pre_canceling (sep (EthernetHeader h a) R m /\ Rest h).
Proof.
  intros.
  purify.
  eexists (mkEthernetHeader _ _ _).

  step. step. step. step. step. step. step. step. step. step. step. step. step.
  step. step. step. step. step.
  { step. }

  undo_step.

  lazymatch type of H with
  | context[EthernetHeader] => idtac
  | _ => fail "folding failed"
  end.
Abort.

Set Default Proof Mode "Ltac2".

(* TODO preserve order of memory hyps *)
(* TODO always put var m at beginning of then/else branch scope so that it doesn't
   move later *)

Definition min3_mem: {f: list string * list string * cmd &
  forall fs t m a b c old_r pa pb pc pr (R: mem -> Prop),
    <{ * uint 32 a pa
       * uint 32 b pb
       * uint 32 c pc
       * uint 32 old_r pr
       * R }> m ->
    vc_func fs f t m [|pa; pb; pc; pr|] (fun t' m' retvs =>
      t' = t /\ retvs = nil /\
      <{ * uint 32 a pa
         * uint 32 b pb
         * uint 32 c pc
         * uint 32 (Z.min a (Z.min b c)) pr
         * R }> m'
  )}.                                                                           .**/
{                                                                          /**. .**/
  if (load4(pa) <= load4(pb) && load4(pa) <= load4(pc)) {                  /**. .**/
    store4(pr, load4(pa));                                                 /**. .**/
  } else {                                                                 /**. .**/
    if (load4(pb) <= load4(pa) && load4(pb) <= load4(pc)) {                /**. .**/
      store4(pr, load4(pb));                                               /**. .**/
    } else {                                                               /**. .**/
      store4(pr, load4(pc));                                               /**. .**/
    }                                                                      /**. .**/
  }                                                                        /**.
(* TODO: stepify after_if *)
(* TODO: trace equality *)
(* TODO: speed up postcondition proving *)                                      .**/
}                                                                          /**.
Defined.

Goal False.
  ltac1:(let r := eval unfold min3_mem in
  match min3_mem with
  | existT _ f _ => f
  end in pose r).
Abort.

(*
(* bs: first 4 bytes: operation, the only supported operation is 1 (squaring)
       next 4 bytes: number to be squared
   output: square-reply: 2, then the squared number *)
Definition variable_size_add: {f: list string * list string * cmd &
  forall fs t m (a n: Z) (bs: list Z) (R: mem -> Prop),
    0 <= a < 2 ^ 32 ->
    0 <= n < 2 ^ 32 ->
    <{ * array_old (value access_size.one) bs a
       * R }> m ->
    len bs = n ->
    vc_func fs f t m [| a; n |] (fun t' m' retvs => True)
      (* TODO can we infer a reasonable postcondition on-the-go? *)
  }.
.**/
{                                                                        /**.


    eapply (wp_if_bool_dexpr _ live_expr:(n == 8 && load4(a) == 1)).

    eval_dexpr_step.
    eval_dexpr_step.
    eval_dexpr_step.
    eval_dexpr_step.

(*
 .**/
  if (n == 8 && load4(a) == 1) {                                         /**.
*)
Abort.


Definition arp: {f: list string * list string * cmd &
  forall fs t m (a n: Z) (bs: list Z) (R: mem -> Prop),
    0 <= a < 2 ^ 32 ->
    0 <= n < 2 ^ 32 ->
    <{ * bs @@ a : Array (UInt 8) n
       * R }> m ->
    vc_func fs f t m [| a; n |] (fun t' m' retvs => True)
      (* TODO can we infer a reasonable postcondition on-the-go? *)
  }.
.**/
{                                                                        /**. .**/
  uintptr_t doReply = 0;                                                 /**. .**/

  if (n == 64) {                                                         /**.

rename H1 into Hm.
eapply (bytearray_to_record (EthernetPacket ARPPacket)) in Hm.
(* TODO n is bound using =, but doReply is bound using :=, consolidate? *)
2: subst n; reflexivity.
destruct Hm as (p & Hm).
split_off_field a "etherType" Hm.
split_off_field a "payload" Hm.
split_off_field (a+14) "htype" Hm.
(*
Close Scope sep_bullets_scope. {
Undelimit Scope sep_scope. {
*)

(*
      if ((load2(ethbuf @ (@etherType ARPPacket)) == ETHERTYPE_ARP_LE) &
          (load2(ethbuf @ (@payload ARPPacket) @ htype) == HTYPE_LE) &
          (load2(ethbuf @ (@payload ARPPacket) @ ptype) == PTYPE_LE) &
          (load1(ethbuf @ (@payload ARPPacket) @ hlen) == HLEN) &
          (load1(ethbuf @ (@payload ARPPacket) @ plen) == PLEN) &
          (load1(ethbuf @ (@payload ARPPacket) @ oper) == OPER_REQUEST)) /*split*/ { /*$.
*)
Abort.

#[export] Hint Rewrite List__repeat_0 : fwd_rewrites.

Require Import coqutil.Tactics.syntactic_unify.

(*
Ltac solve_list_eq :=
  list_simpl_in_goal; try syntactic_exact_deltavar (@eq_refl _ _).
*)

Tactic Notation "loop" "invariant" "above" ident(i) :=
  let n := fresh "Scope0" in pose proof (mk_scope_marker LoopInvariant) as n;
  move n after i.

Ltac indep H :=
  lazymatch goal with
  | Sc: scope_marker LoopInvariant |- _ => move H after Sc
  end.

(* redefinition to accept a constr (as returned by find) in the occurrence clause: *)
Tactic Notation "Replace" constr(lhs) "with" constr(rhs) "in" constr(hypname)
       "by" tactic3(tac) := replace lhs with rhs in hypname by tac.

Definition memset: {f: list string * list string * cmd &
  forall fs t m (a b n: Z) (bs: list Z) (R: mem -> Prop),
    0 <= a < 2 ^ 32 ->
    0 <= b < 2 ^ 8 ->
    0 <= n < 2 ^ 32 ->
    <{ * array_old (value access_size.one) bs a
       * R }> m ->
    n = len bs ->
    vc_func fs f t m [| a; b; n |] (fun t' m' retvs =>
      t' = t /\
      <{ * array_old (value access_size.one) (List.repeatz b n) a
         * R }> m' /\
      retvs = nil)
  }.
.**/
{                                                                        /**. .**/
  uintptr_t i = 0;                                                       /**.

Replace bs with (List.repeatz b i ++ bs[i:]) in (find! @sep) by egg_simpl_or_prove.
loop invariant above i.
indep (find! (n = ??)).
assert (0 <= i <= n) by ZWords.
clearbody i.

.**/
  while (i < n) /* decreases (n - i) */ {                                /**. .**/
    store1(a + i, b);                                                    /**.

Abort.
(*

(* TODO: automate prettification steps below *)
rewrite Z.div_1_r in *.
rewrite List.repeat_length in *.
Replace (S (i to nat) - i to nat + i to nat) with (i to nat + 1%nat) in * by ZnWords.

.**/
     i = i + 1;                                                          /**. .**/
  }                                                                      /**.

{
  Replace ((i_0 + 1 to word) to nat) with (i_0 to nat + 1 to nat) by ZnWords.
  rewrite List.repeat_app.
  rewrite <- List.app_assoc.
  assumption.
}

  fwd.
  Replace (i to nat) with (List.length bs) in * by ZnWords.
.**/
}                                                                        /**.
Defined.

Goal False.
  let r := eval unfold memset in
  match memset with
  | existT _ f _ => f
  end in pose r.
Abort.

Definition merge_tests: {f: list string * list string * cmd &
  forall fs t (m: mem) (a: word) (vs: list word) R,
    <{ * a --> vs
       * R }> m ->
    List.length vs = 3%nat ->
    vc_func fs f t m [| a |] (fun t' m' retvs => False)
  }. .**/
{                                                                        /**. .**/
  uintptr_t w0 = load(a);                                                /**. .**/
  uintptr_t w1 = load(a+4);                                              /**. .**/
  uintptr_t w2 = load(a+8);                                              /**. .**/
  if (w1 < w0 && w1 < w2) {                                              /**. .**/
    store(a, w1);                                                        /**. .**/
    w1 = w0;                                                             /**.

assert (exists foo: Z, foo + foo = 2) as Foo. {
  exists 1. reflexivity.
}
destruct Foo as (foo & Foo).

move m at bottom.
move w1 at bottom.

assert (exists bar: nat, (bar + bar = 4 * Z.to_nat foo)%nat) as Bar. {
  exists 2%nat. blia.
}
destruct Bar as (bar & Bar).
pose (baz := foo + foo).
assert (w1 + w0 + word.of_Z baz = word.of_Z baz + w1 + w1) as E by ZnWords.
rename w1 into w1tmp.
pose (w1 := w0 + word.of_Z baz - word.of_Z baz).
move w1 after w1tmp.
replace w1tmp with w1 in * by ZnWords. clear w1tmp.

.**/
  } else {                                                               /**. .**/
}                                                                        /**. .**/
                                                                         /**.
Abort.

Hint Extern 4 (Permutation _ _) =>
  eauto using perm_nil, perm_skip, perm_swap, perm_trans
: prove_post.

Definition sort3: {f: list string * list string * cmd &
  forall fs t (m: mem) (a: word) (vs: list word) R,
    <{ * a --> vs
       * R }> m ->
    List.length vs = 3%nat ->
    vc_func fs f t m [| a |] (fun t' m' retvs =>
      exists v0 v1 v2,
        t' = t /\
        Permutation vs [| v0; v1; v2 |] /\
        v0 to Z <= v1 to Z <= v2 to Z /\
        <{ * a --> [| v0; v1; v2 |]
           * R }> m'
  )}. .**/
{                                                                        /**. .**/
  uintptr_t w0 = load(a);                                                /**. .**/
  uintptr_t w1 = load(a+4);                                              /**. .**/
  uintptr_t w2 = load(a+8);                                              /**. .**/
  if (w1 <= w0 && w1 <= w2) {                                            /**. .**/
    store(a, w1);                                                        /**. .**/
    w1 = w0;                                                             /**. .**/
  } else {                                                               /**. .**/
    if (w2 <= w0 && w2 <= w1) {                                          /**. .**/
      store(a, w2);                                                      /**. .**/
      w2 = w0;                                                           /**. .**/
    } else {                                                             /**. .**/
    }                                                          /**. .**/ /**. .**/
  }                                                            /**. .**/ /**. .**/
  if (w2 < w1) {                                                         /**. .**/
    store(a+4, w2);                                                      /**. .**/
    store(a+8, w1);                                                      /**. .**/
  } else {                                                               /**. .**/
    store(a+4, w1);                                                      /**. .**/
    store(a+8, w2);                                                      /**. .**/
  }                                                            /**. .**/ /**. .**/
}                                                                        /**.
Defined.

(* Print Assumptions sort3. *)

(* TODO: write down postcondition only at end *)
Definition swap_locals: {f: list string * list string * cmd &
  forall fs tr m a b,
    vc_func fs f tr m [| a; b |] (fun tr' m' retvs =>
      tr' = tr /\ m' = m /\ retvs = [| b; a |]
  )}.
  (* note: we could just do skip and return ["b", "a"] *)                       .**/
{                                                                          /**. .**/
  uintptr_t t = a;                                                         /**. .**/
  a = b;                                                                   /**. .**/
  b = t;                                                                   /**. .**/
  uintptr_t res1 = a;                                                      /**. .**/
  uintptr_t res2 = b;                                                      /**. .**/
  return res1, res2;                                                       /**. .**/
}                                                                          /**.
Defined.

(* TODO: write down postcondition only at end *)
Definition swap: {f: list string * list string * cmd &
  forall fs t (m: mem) (a_addr b_addr a b: word) R,
    <{ * a_addr ~> a
       * b_addr ~> b
       * R
    }> m ->
    vc_func fs f t m [| a_addr; b_addr |] (fun t' m' retvs =>
      <{ * a_addr ~> b
         * b_addr ~> a
         * R
      }> m' /\ retvs = [] /\ t' = t
  )}.
#*/ {                                                                        /*.
#*/   uintptr_t t = load(a_addr);                                            /*.
#*/   store(a_addr, load(b_addr));                                           /*.
#*/   store(b_addr, t);                                                      /*.
#*/ }                                                                        /*.
Defined.

Goal False.
  let r := eval unfold swap_locals in
  match swap_locals with
  | existT _ f _ => f
  end in pose r.
Abort.

Definition foo(a b: word): word := a + b.

Lemma test: forall a b, foo a b = foo b a.
Proof. unfold foo. intros. ring. Qed.

About test.
(* test : forall a b : word, foo a b = foo b a *)

End LiveVerif.

About test.
(*
test :
forall
  {word : word
            (BinNums.Zpos
               (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO BinNums.xH))))))},
word.ok word -> forall a b : word, foo a b = foo b a
 *)

Comments !EOF .**/ //.


  Fixpoint remove_seq_nat(start: Z)(len: nat)(m: mem): mem :=
    match len with
    | O => m
    | S n => map.remove (remove_seq_nat (wadd start 1) n m) start
    end.

  Definition remove_seq(start len: Z): mem -> mem := remove_seq_nat start (Z.to_nat len).

  Definition get_seq(start len: Z)(m: mem): list byte :=
    List.map (fun ofs => get_or_zero (wadd start (Z.of_nat ofs)) m)
             (List.seq 0 (Z.to_nat len)).

  Definition has_seq(start len: Z)(m: mem): Prop :=
    List.Foral
*)
*)
