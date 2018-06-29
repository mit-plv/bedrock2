Require Import compiler.Common.
Require Import compiler.FlatImp.
Require Import compiler.StateCalculus.
Require Import compiler.NameGen.
Require Import compiler.NameWithEq.
Require Import riscv.util.BitWidths.
Require Import Coq.Lists.List.

Section RegAlloc.

  Context {Bw: BitWidths}.

  Context {VarName: NameWithEq}.
  Context {RegisterName: NameWithEq}.
  Context {FuncName: NameWithEq}.
  
  Notation var := (@name VarName).
  Notation register := (@name RegisterName).
  Notation func := (@name FuncName).

  Existing Instance eq_name_dec.

  Context {vars: Type}.
  Context {varset: set vars var}.

  Context {registers: Type}.
  Context {registerset: set registers register}.

  Context {alloc: Type}.
  Context {allocMap: Map alloc var register}.

  Local Notation stmt := (@stmt Bw VarName FuncName).

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

  Definition TODO{T: Type}: T. Admitted.
  
  Definition restrict(s: alloc)(newDomain: vars): alloc := TODO.

  (* TODO implement, and treat the case where no more registers are available *)
  Definition pick(rs: registers): (register * registers) := TODO.

  Definition domain: alloc -> vars := TODO.
  Definition range: alloc -> registers := TODO.

  Definition start_interval(current: vars * registers * alloc)(x: var)
    : vars * registers * alloc :=
    let '(o, a, m) := current in
    let o := union o (singleton_set x) in
    let '(r, a) := pick a in
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

  Variable dummy_register: register.

  Definition make_total(m: alloc): var -> register :=
    fun x => match get m x with
          | Some r => r
          | None => dummy_register
          end.

  Definition apply_alloc(m: var -> register): stmt -> @FlatImp.stmt Bw RegisterName FuncName :=
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
      | SCall argnames fname resnames => SCall (map m argnames) fname (map m resnames)
      end.

  Variable available_registers: registers. (* r1..r31 on RISCV *)

  Definition register_allocation(s: stmt): @FlatImp.stmt Bw RegisterName FuncName :=
    let '(_, _, m) := regalloc empty_set available_registers empty s empty_set in
    apply_alloc (make_total m) s.

  (******* below: failed versions: **********)

  (* This is too verbose: *)
  Fixpoint regalloc'''
           (occupants: vars)       (* variables which currently occupy a register *)
           (available: registers)  (* registers not used currently *)
           (assignment: alloc)     (* mapping from variables to registers *)
           (s: stmt)               (* current sub-statement 
                                      Note: After s, more statements will be executed! *)
           (afterlive: vars)       (* variables which have a life after statement s *)
    : (vars * registers * alloc)   (* new occupants, new available registers, new assignment *)
    :=
    (* let's see if we can add any available registers: *)
    let deadvars := diff occupants (union (live s) afterlive) in
    let registers_of_deadvars := range (restrict assignment deadvars) in
    (* What if a live variable x and a dead variable y are mapped to the same register r?
       Then if y is in deadvars, x is not in "occupants", because any two vars mapped to the
       same register cannot be in "occupants" at the same time.
       So adding r to the available registers is safe because it is not needed by x nor by y
       any more. *)
    let available := union available registers_of_deadvars in
    let occupants := live s in
    let nop := (occupants, available, assignment) in
    match s with
    | SLoad x _ | SLit x _ | SOp x _ _ _ | SSet x _ =>
        match get assignment x with
        | Some rx => nop (* nothing to do because no new interval starts *)
        | None => (* new interval starts *)
            let occupants := union occupants (singleton_set x) in
            let '(r, available) := pick available in
            let assignment := put assignment x r in
            (occupants, available, assignment)
        end
    | SStore x y => nop
    | SIf cond s1 s2   => TODO (*
        let '(occupants1, available1, assignment1) :=
          regalloc''' occupants available  assignment  s1 in
        let '(occupants2, available2, assignment2) := 
          regalloc''' occupants available1 assignment1 s1 in
        (union occupants1 occupants2, available2, assignment2) *)
    | SLoop s1 cond s2 => TODO
    | SSeq s1 s2 =>
        let '(occupants, available, assignment) :=
          regalloc''' occupants available assignment s1 (union (live s2) afterlive) in
        regalloc''' occupants available assignment s2 afterlive
    | SSkip => nop
    | SCall argnames fname resnames => TODO
    end.
  
  Fixpoint regalloc''(active: vars)(available: registers)(assignment: alloc)(s: stmt):
    (vars * registers * alloc) :=
    (* let's see if we can add any available registers: *)
    let deadvars := diff active (live s) in (* <-- this should be a bigger set (really all) *)
    let registers_of_deadvars := range (restrict assignment deadvars) in
    (* What if a live variable x and a dead variable y are mapped to the same register r?
       Then if y is in deadvars, x is not in "active", because any two vars mapped to the
       same register cannot be in "active" at the same time.
       So adding r to the available registers is safe because it is not needed by x nor by y
       any more. *)
    let available := union available registers_of_deadvars in
    let active := live s in
    let nop := (active, available, assignment) in
    match s with
    | SLoad x _ | SLit x _ | SOp x _ _ _ | SSet x _ =>
        match get assignment x with
        | Some rx => nop (* nothing to do because no new interval starts *)
        | None => (* new interval starts *)
            let active := union active (singleton_set x) in
            let '(r, available) := pick available in
            let assignment := put assignment x r in
            (active, available, assignment)
        end
    | SStore x y => nop
    | SIf cond s1 s2   =>
        let '(active1, available1, assignment1) := regalloc'' active available  assignment  s1 in
        let '(active2, available2, assignment2) := regalloc'' active available1 assignment1 s1 in
        (union active1 active2, available2, assignment2)
    | SLoop s1 cond s2 => TODO
    | SSeq s1 s2       =>
        let '(active, available, assignment) := regalloc'' active available assignment s1 in
        regalloc'' active available assignment s2
    | SSkip => nop
    | SCall argnames fname resnames => TODO
    end.

  Fixpoint regalloc'(available: registers)(assignment: alloc)(s: stmt): (registers * alloc) :=
    (* let's see if we can add any available registers: *)
    let deadvars := diff (domain assignment) (live s) in
    let registers_of_deadvars := range (restrict assignment deadvars) in
    (* What if a live variable x and a dead variable y are mapped to the same register r?
       Then y is in deadvars, so r will be added to the available registers, even though
       it is still needed to hold the value of x -> bad *)
    let available := union available registers_of_deadvars in
    match s with
    | SLoad x _ | SLit x _ | SOp x _ _ _ | SSet x _ =>
        match get assignment x with
        | Some rx => (* nothing to do because no new interval starts *)
            (available, assignment)
        | None => (* new interval starts *)
            let '(r, available) := pick available in
            let assignment := put assignment x r in
            (available, assignment)
        end
    | SStore x y   => TODO
    | SIf cond s1 s2   => TODO
    | SLoop s1 cond s2 => TODO
    | SSeq s1 s2       => TODO
    | SSkip => (available, assignment)
    | SCall argnames fname resnames => TODO
    end.

End RegAlloc.
