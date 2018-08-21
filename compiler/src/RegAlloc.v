Require Import compiler.FlatImp.
Require Import compiler.StateCalculus.
Require Import compiler.NameGen.
Require Import compiler.NameWithEq.
Require Import riscv.util.BitWidths.
Require Import Coq.Lists.List.
Require Import compiler.util.Common.
Require Import riscv.Utility.


Section RegAlloc.

  Context {mword: Set}.
  Context {MW: MachineWidth mword}.

  Context {VarName: NameWithEq}.
  Context {RegisterName: NameWithEq}.
  Context {FuncName: NameWithEq}.
  
  Notation var := (@name VarName).
  Notation register := (@name RegisterName).
  Notation func := (@name FuncName).

  Existing Instance eq_name_dec.

  Context {allocMap: MapFunctions var register}.
  Notation alloc := (map var register).
  Notation vars := (@set var (@map_domain_set _ _ allocMap)).
  Notation registers := (@set register (@map_range_set _ _ allocMap)).
  (* Alternative way to write the same:
  Existing Instance map_domain_set.
  Existing Instance map_range_set.
  Notation vars := (set var).
  Notation registers := (set register).
  *)

  Local Notation stmt := (@stmt VarName FuncName).

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
    | SLoop s1 cond s2 => union (live s1) (diff (live s2) (certainly_written s1))
    | SSeq s1 s2       => union (live s1) (diff (live s2) (certainly_written s1))
    | SSkip => empty_set
    | SCall argnames fname resnames => of_list argnames
    end.

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

  Definition apply_alloc(m: var -> register): stmt -> @FlatImp.stmt RegisterName FuncName :=
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

  Variable available_registers: registers. (* r1..r31 on RISCV *)

  Definition register_allocation(s: stmt): @FlatImp.stmt RegisterName FuncName :=
    let '(_, _, m) := regalloc empty_set available_registers empty_map s empty_set in
    apply_alloc (make_total m) s.

End RegAlloc.
