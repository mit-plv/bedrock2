Require Import compiler.FlatImp.
Require Import compiler.StateCalculus.
Require Import compiler.NameGen.
Require Import compiler.Decidable.
Require Import compiler.Memory.
Require Import riscv.util.BitWidths.
Require Import Coq.Lists.List.
Require Import compiler.util.Common.
Require Import riscv.Utility.

Section Injective.

  Context {A B: Type} {sf: SetFunctions A}.

  Definition injective_over(f: A -> B)(s: set A): Prop :=
    forall a1 a2, a1 \in s -> a2 \in s -> f a1 = f a2 -> a1 = a2.

  Lemma injective_over_union: forall (f: A -> B) (s1 s2: set A),
      injective_over f (union s1 s2) -> injective_over f s1 /\ injective_over f s2.
  Proof.
    unfold injective_over; intuition (set_solver_generic A).
  Qed.

End Injective.

(* require extensionality, and usually only needed for debugging *)
Section EmptySetOps.

  Context {A: Type} {sf: SetFunctions A}.

  Axiom union_empty_l: forall (s: set A), union empty_set s = s.
  Axiom union_empty_r: forall (s: set A), union s empty_set = s.
  Axiom intersect_empty_l: forall (s: set A), intersect empty_set s = empty_set.
  Axiom intersect_empty_r: forall (s: set A), intersect s empty_set = empty_set.
  Axiom diff_empty_l: forall (s: set A), diff empty_set s = empty_set.
  Axiom diff_empty_r: forall (s: set A), diff s empty_set = s.

End EmptySetOps.

Hint Rewrite
    @union_empty_l
    @union_empty_r
    @intersect_empty_l
    @intersect_empty_r
    @diff_empty_l
    @diff_empty_r
: rew_EmptySetOps.

Notation "｛｝" := (@empty_set _ _) : set_scope.

Notation "｛ x ｝" := (singleton_set x) (format "｛ x ｝") : set_scope.

Notation "E ∪ F" := (union E F)
  (at level 37, F at level 0) : set_scope.

Notation "E ∩ F" := (intersect E F)
  (at level 36, F at level 0) : set_scope.

Notation "E — F" := (diff E F)
  (at level 35, F at level 0) : set_scope.

Notation "x ∈ E" := (contains E x) (at level 39) : set_scope.

Notation "x ∉ E" := (~ contains E x) (at level 39) : set_scope.

Notation "E ⊆ F" := (subset E F)
  (at level 38) : set_scope.


(*
Notation "\{}" := (@empty_set _ _) : set_scope.

Notation "\{ x }" := (singleton_set x) : set_scope.

Notation "E \u F" := (union E F)
  (at level 37, F at level 0) : set_scope.

Notation "E \n F" := (intersect E F)
  (at level 36, F at level 0) : set_scope.

Notation "E \- F" := (diff E F)
  (at level 35, F at level 0) : set_scope.

Notation "x \in E" := (contains x E) (at level 39) : set_scope.

Notation "x \notin E" := (~ contains x E) (at level 39) : set_scope.

Notation "E \c F" := (subset E F)
  (at level 38) : set_scope.
*)

Section RegAlloc.

  Context {mword: Set}.
  Context {MW: MachineWidth mword}.

  Variable var: Set.
  Context {var_eq_dec: DecidableEq var}.
  Variable register: Set.
  Context {register_eq_dec: DecidableEq register}.
  Variable func: Set.
  Context {func_eq_dec: DecidableEq func}.

  Context {allocMap: MapFunctions var register}.
  Notation alloc := (map var register).
  Notation vars := (@set var (@map_domain_set _ _ allocMap)).
  Notation registers := (@set register (@map_range_set _ _ allocMap)).
  Existing Instance map_domain_set.
  Existing Instance map_range_set.
  (* don't do this, it might pick up the wrong typeclasses
  Notation vars := (set var).
  Notation registers := (set register).
  *)

  Local Notation stmt  := (FlatImp.stmt var func).      (* input type *)
  Local Notation stmt' := (FlatImp.stmt register func). (* output type *)

  Ltac set_solver := set_solver_generic var.

  (* set of variables which is certainly written while executing s *)
  Fixpoint certainly_written(s: stmt): vars :=
    match s with
    | SLoad x y    => singleton_set x
    | SStore x y   => singleton_set x
    | SLit x v     => singleton_set x
    | SOp x op y z => singleton_set x
    | SSet x y     => singleton_set x
    | SIf cond s1 s2 => intersect (certainly_written s1) (certainly_written s2)
    | SLoop s1 cond s2 => certainly_written s1
    | SSeq s1 s2 => union (certainly_written s1) (certainly_written s2)
    | SSkip => empty_set
    | SCall argnames fname resnames => of_list resnames
    end.

  (* set of variables which is live before executing s *)
  Fixpoint live(s: stmt): vars :=
    match s with
    | SLoad x y    => singleton_set y
    | SStore x y   => union (singleton_set x) (singleton_set y)
    | SLit x v     => empty_set
    | SOp x op y z => union (singleton_set y) (singleton_set z)
    | SSet x y     => singleton_set y
    | SIf cond s1 s2   => union (singleton_set cond) (union (live s1) (live s2))
    | SLoop s1 cond s2 => union (live s1) (diff (union (singleton_set cond) (live s2))
                                                (certainly_written s1))
    | SSeq s1 s2       => union (live s1) (diff (live s2) (certainly_written s1))
    | SSkip => empty_set
    | SCall argnames fname resnames => of_list argnames
    end.

  Definition holds_forall_livesets(P: vars -> Prop): stmt -> Prop :=
    fix rec(s: stmt) :=
      P (live s) /\
      match s with
      (* recursive cases: *)
      | SIf _ s1 s2 | SLoop s1 _ s2 | SSeq s1 s2 => rec s1 /\ rec s2
      (* non-recursive cases: *)
      | _ => True
      end.

  Definition injective_over_all_livesets{B: Type}(f: var -> B): stmt -> Prop :=
    holds_forall_livesets (fun liveset => injective_over f liveset).

  Variable dummy_register: register.

  Definition start_interval(current: vars * registers * alloc)(x: var)
    : vars * registers * alloc :=
    let '(o, a, m) := current in
    let o := union o (singleton_set x) in
    let '(r, a) := pick_or_else a dummy_register in
    let m := put m x r in
    (o, a, m).

  Fixpoint regalloc
           (o: vars)             (* occupants: variables which currently occupy a register *)
           (a: registers)        (* available registers (those not used currently) *)
           (m: alloc)            (* mapping from variables to registers *)
           (s: stmt)             (* current sub-statement *)
           (l: vars)             (* variables which have a life after statement s *)
    : (vars * registers * alloc) (* new occupants, new available registers, new mapping *)
    :=
    let o_original := o in
    (* these are the variables which actually deserve to occupy a register: *)
    let o := union (live s) (diff l (certainly_written s)) in
    (* intervals which ended... *)
    let dead := diff o_original o in
    (* ... allow allow us to add new available registers to a: *)
    let a := union a (range (restrict m dead)) in
    match s with
    | SLoad x _ | SLit x _ | SOp x _ _ _ | SSet x _ =>
        match get m x with
        | Some rx => (o, a, m) (* nothing to do because no new interval starts *)
        | None    => start_interval (o, a, m) x
        end
    | SStore x y => (o, a, m)
    | SIf cond s1 s2   =>
        let '(o1, a1, m1) := regalloc o a  m  s1 l in
        let '(o2, a2, m2) := regalloc o a1 m1 s2 l in
        (union o1 o2, a2, m2)
    | SLoop s1 cond s2 =>
        let '(o, a, m) := regalloc o a m s1 (union (union (singleton_set cond) (live s2)) l) in
        regalloc o a m s2 l
    | SSeq s1 s2 =>
        let '(o, a, m) := regalloc o a m s1 (union (live s2) l) in
        regalloc o a m s2 l
    | SSkip => (o, a, m)
    | SCall argnames fname resnames => fold_left start_interval resnames (o, a, m)
    end.

  Ltac head e :=
    match e with
    | ?a _ => head a
    | _ => e
    end.

  Goal forall (s: stmt), False.
    intro s.
    destruct s eqn: E;
    match type of E with
    | _ = ?r => let h := head r in idtac "| set ( case :=" h ")"
    end.
  Abort.

  Lemma regalloc_ok: forall  (s: stmt) (l: vars) (o o': vars) (a a': registers) (m m': alloc),
      injective_over (get m) o ->
      injective_over (get m) l ->
      subset (live s) o ->
      subset l (union o (certainly_written s)) ->
      regalloc o a m s l = (o', a', m') ->
      injective_over_all_livesets (get m') s /\ injective_over (get m') l.
  Proof.
    induction s;
      intros;
      [ set ( case := @SLoad )
      | set ( case := @SStore )
      | set ( case := @SLit )
      | set ( case := @SOp )
      | set ( case := @SSet )
      | set ( case := @SIf )
      | set ( case := @SLoop )
      | set ( case := @SSeq )
      | set ( case := @SSkip )
      | set ( case := @SCall ) ];
      move case at top;
      repeat destruct_one_match;
      simpl in *;
      repeat destruct_one_match_hyp;
      try destruct_pair_eqs;
      subst.

   (*   unfold injective_over in * *)
   (*   try solve [ intuition (state_calc_generic var register) ]. *)

    Focus 11.
    {
      repeat match goal with
      | IH: _, E: regalloc _ _ _ _ _  = (_, _, _) |- _ => specialize IH with (5 := E)
      end.

      repeat match goal with
      | E: regalloc _ _ _ _ _  = (_, _, _) |- _ => clear E
      end.

      unfold injective_over in *.

      destruct IHs1.
      - clear IHs2. set_solver.
      - clear IHs2.
        (* not solved by set_solver *)

        forget (certainly_written s1) as cws1.
        forget (live s1) as ls1.
        forget (live s2) as ls2.


(* intro as much as we can *)
repeat intro.

(* map to fun *)
repeat match goal with
       | m: map _ _ |- _ =>
         let f := fresh "f" in
         let H := fresh "HE" in
         remember (get m) as f eqn: H;
           clear m H
       end.

(* clear everything except used vars and Props *)
repeat match goal with
       | H: ?T |- _ =>
         match type of T with
         | Prop => fail 1
         | _ => clear H
         end
       end.

Notation reg := (option register).

Inductive ____BEGIN_counterexample____: Prop :=
  mk_BEGIN_counterexample: ____BEGIN_counterexample____.
Inductive ____END_counterexample____: Prop :=
  mk_END_counterexample: ____END_counterexample____.
Inductive ____cardinality_constraint: Prop :=
  mk_cardinality_constraint: ____cardinality_constraint.

Tactic Notation "(model" tactic(t) :=
  pose proof mk_BEGIN_counterexample; t.
Tactic Notation ")" :=
  pose proof mk_END_counterexample.
Tactic Notation ";;" "universe" "for" constr(T) ":" tactic(t) := t.
Tactic Notation ";;" ident(v1) tactic(t) := t.
Tactic Notation ";;" ident(v1) ident(v2) tactic(t) := t.
Tactic Notation ";;" ident(v1) ident(v2) ident(v3) tactic(t) := t.
Tactic Notation ";;" ident(v1) ident(v2) ident(v3) ident(v4) tactic(t) := t.
Tactic Notation ";;" "-----------" tactic(t) := t.
Tactic Notation ";;" "definitions" "for" "universe" "elements:" tactic(t) := t.
Tactic Notation "(declare-fun" ident(x) "()" constr(T) ")" tactic(t) :=
  (assert (x: T) by admit); t.
Tactic Notation "(define-fun" ident(x) "()" constr(T) constr(v) ")" tactic (t) :=
  let E := fresh "E" in (assert (x = v) as E by admit);
  rewrite E in *;
  t.
Tactic Notation "(define-fun" ident(f) "(" "(" ident(x) constr(T) ")" ")" constr(U)
       constr(body) ")" tactic(t) :=
  let E := fresh "E" in (assert (f = fun (x: T) => body) as E by admit);
  rewrite E in *;
  t.
Tactic Notation "(define-fun" ident(f) "(" "(" ident(x) constr(T) ")" ")" "Bool"
       constr(body) ")" tactic(t) :=
  let E := fresh "E" in (assert (f = empty_set) as E by admit);
  rewrite E in *;
  t.
Tactic Notation ";;" "cardinality" "constraint:" constr(P) tactic(t) :=
  pose proof mk_cardinality_constraint; assert P by admit; t.

(* Gallina notations to parse cardinality constraints: *)
Notation "'forall' '(' '(' a T ')' ')' body" := (forall (a: T), body)
   (at level 200, a at level 0, T at level 0, body at level 0, only parsing).
Notation "'or' A B" := (Logic.or A B)
   (at level 10, A at level 0, B at level 0, only parsing).
Notation "= A B" := (@eq _ A B)
   (at level 10, A at level 0, B at level 0, only parsing).


(model
  ;; universe for var:
  ;;   var_val_1 var_val_0
  ;; -----------
  ;; definitions for universe elements:
  (declare-fun var_val_1 () var) idtac.
  (declare-fun var_val_0 () var)
  ;; cardinality constraint:
  (forall ((x var)) (or (= x var_val_1) (= x var_val_0)))
  ;; -----------
  ;; universe for reg:
  ;;   reg_val_0
  ;; -----------
  ;; definitions for universe elements:
  (declare-fun reg_val_0 () reg)
  ;; cardinality constraint:
  (forall ((x reg)) (= x reg_val_0))
  ;; -----------
  (define-fun cond () var
    var_val_1)
  (define-fun a2 () var
    var_val_1)
  (define-fun a1 () var
    var_val_0)
  (define-fun l ((x_1 var)) Bool
    false)
  (define-fun f0 ((x_1 var)) reg
    reg_val_0)
).

Ltac disj_to_set d :=
  lazymatch d with
    | (_ = ?v1 \/ ?rest) =>
      let s := disj_to_set rest in
      constr:(union (singleton_set v1) s)
    | (_ = ?v1) => constr:(singleton_set v1)
    | _ => fail "did not expect" d
  end.

Ltac universe_of T :=
  match goal with
  | H: forall (x: T), _ |- _ =>
    let dummyT := match type of H with
                  | forall (x: T), x = ?v1 => constr:(v1)
                  | forall (x: T), x = ?v1 \/ _ => constr:(v1)
                  end in
    let P' := type of (H dummyT) in
    disj_to_set P'
  end.

match type of ls2 with
| set ?T =>
  let r := universe_of T in idtac r
end.

(*
let P' := constr:(reg_val_0 = reg_val_0) in
    tryif constr:(@singleton_set reg _) then
      (let r := lazymatch P' with
                | (_ = ?v1 \/ ?rest) =>
                  let s := disj_to_set rest in
                  constr:(union (singleton_set v1) s)
                | (_ = ?v1) => constr:(singleton_set v1)
                | _ => fail "did not expect" P'
                end in
      idtac r)
    else fail 1000 "no set instance found".

match type of f0 with
| _ ->  ?T =>
  match goal with
  | H: forall (x: T), _ |- _ =>
    let dummyT := match type of H with
                  | forall (x: T), x = ?v1 => constr:(v1)
                  | forall (x: T), x = ?v1 \/ _ => constr:(v1)
                  end in
    let P' := type of (H dummyT) in
    let r :=   lazymatch P' with
               | (_ = ?v1 \/ ?rest) =>
                 let s := disj_to_set rest in
                 constr:(union (singleton_set v1) s)
               | (_ = ?v1) => constr:(singleton_set v1)
               | _ => fail "did not expect" P'
               end in
    idtac r
  end
end.

let T := type of reg_val_0 in let r := universe_of T in idtac r.

match type of ls2 with
| set ?T =>
  match goal with
  | H: forall (x: T), _ |- _ =>
    let dummyT := match type of H with
                  | forall (x: T), x = ?v1 => constr:(v1)
                  | forall (x: T), x = ?v1 \/ _ => constr:(v1)
                  end in
    let P' := type of (H dummyT) in
    let r := disj_to_set P' in
    idtac r
  end
end.

match type of H8 with
  | forall (x: ?T), ?P =>
    idtac P;
    let dummyT := match P with
                  | x = ?v1 => constr:(v1)
                  | x = ?v1 \/ _ => constr:(v1)
                  end in
    let P' := type of (H dummyT) in idtac P'
end.
*)

(* TODO: this part

  (define-fun ls2 ((x_1 var)) Bool
    true)
  (define-fun cws1 ((x_1 var)) Bool
    true)
  (define-fun o ((x_1 var)) Bool
    false)
  (define-fun ls1 ((x_1 var)) Bool
    false)

Problem: how to map functions back to sets?

while keeping functions (f0: var -> reg) *)

        Open Scope set_scope.

        (* here is better *)

  Admitted.

  Inductive inspect{T: Type}: T -> Prop := .

  Goal forall o a m l cond s1 s2 s3, inspect (regalloc o a m (SSeq (SIf cond s1 s2) s3) l).
    intros.
    let b := eval cbv delta [regalloc] in regalloc in change regalloc with b.
    cbv beta iota. fold regalloc.
    simpl live.
  Abort.

  Definition make_total(m: alloc): var -> register :=
    fun x => match get m x with
          | Some r => r
          | None => dummy_register
          end.

  Definition apply_alloc(m: var -> register): stmt -> stmt' :=
    fix rec(s: stmt) :=
      match s with
      | SLoad x y => SLoad (m x) (m y)
      | SStore x y => SStore (m x) (m y)
      | SLit x v => SLit (m x) v
      | SOp x op y z => SOp (m x) op (m y) (m z)
      | SSet x y => SSet (m x) (m y)
      | SIf cond s1 s2   => SIf (m cond) (rec s1) (rec s2)
      | SLoop s1 cond s2 => SLoop (rec s1) (m cond) (rec s2)
      | SSeq s1 s2 => SSeq (rec s1) (rec s2)
      | SSkip => SSkip
      | SCall argnames fname resnames => SCall (List.map m argnames) fname (List.map m resnames)
      end.

  Context {RF: MapFunctions var mword}.
  Notation RegisterFile := (map var mword).

  Context {RF': MapFunctions register mword}.
  Notation RegisterFile' := (map register mword).

  Notation Mem := (@mem mword).

  Context {funcMap: MapFunctions func (list var * list var * stmt)}.
  Context {funcMap': MapFunctions func (list register * list register * stmt')}.

  Definition eval: nat -> RegisterFile -> Mem -> stmt -> option (RegisterFile * Mem) :=
    FlatImp.eval_stmt var func empty_map.

  Definition eval': nat -> RegisterFile' -> Mem -> stmt' -> option (RegisterFile' * Mem) :=
    FlatImp.eval_stmt register func empty_map.

  Lemma apply_alloc_ok: forall (mapping: var -> register) (fuel: nat) (s: stmt) (l: vars)
                          (rf1 rf2: RegisterFile) (rf1': RegisterFile') (m1 m2: Mem),
      injective_over_all_livesets mapping s ->
      injective_over mapping l ->
      (forall x, x \in (live s) -> get rf1 x = get rf1' (mapping x)) ->
      eval fuel rf1 m1 s = Some (rf2, m2) ->
      exists (rf2': RegisterFile'),
        eval' fuel rf1' m1 (apply_alloc mapping s) = Some (rf2', m2) /\
        (forall x, x \in l -> get rf2 x = get rf2' (mapping x)).
  Proof.
  Admitted.

  Variable available_registers: registers. (* r1..r31 on RISCV *)

  (* c: mapping of registers we care about at end (which contain results we want to read) *)
  Definition register_mapping(s: stmt)(c: alloc): var -> register :=
    let '(_, _, m) := regalloc empty_set (diff available_registers (range c)) c s (domain c) in
    (make_total m).

  Definition register_allocation(s: stmt)(c: alloc): stmt' :=
    apply_alloc (register_mapping s c) s.

  Lemma register_allocation_ok: forall (fuel: nat) (s: stmt) (c: alloc)
                                  (rf1 rf2: RegisterFile) (rf1': RegisterFile') (m1 m2: Mem),
      (forall x, get rf1 x = get rf1' (register_mapping s c x)) ->
      eval fuel rf1 m1 s = Some (rf2, m2) ->
      exists (rf2': RegisterFile'),
        eval' fuel rf1' m1 (register_allocation s c) = Some (rf2', m2) /\
        (forall x, x \in domain c -> get rf2 x = get rf2' (register_mapping s c x)).
  Proof.
    intros.
    pose proof (regalloc_ok s (domain c)) as Q.
    destruct (regalloc empty_set (diff available_registers (range c)) c s (domain c))
      as [[? ?] m'] eqn: E.
    specialize Q with (o := empty_set) (a := (diff available_registers (range c))) (m := c).
    specialize Q with (5 := E).
    destruct Q as [I1 I2].
    - admit.
    - admit.
    - admit.
    - pose proof (apply_alloc_ok (register_mapping s c) fuel s (domain c) rf1 rf2 rf1' m1 m2)
        as P.
      specialize P with (4 := H0).
      destruct P as [rf2' [Ev Eq]].
      + unfold register_mapping.
        rewrite E.
        admit. (* lift make_total over injective_over_all_livesets *)
      + unfold register_mapping.
        rewrite E.
        admit. (* lift make_total over injective_over_all_livesets *)
      + intros. apply H.
      + eauto.
  Admitted.

End RegAlloc.
