Require Import compiler.FlatImp.
Require Import compiler.StateCalculus.
Require Import compiler.Decidable.
Require Import Coq.Lists.List.
Require Import riscv.Utility.
Require Import compiler.Op.
Require Import compiler.util.Map.
Require Import compiler.util.Set.

Section TODO.
  Context {K V: Type}.
  Context {Mf: MapFunctions K V}.
  (*
  Axiom get_in_domain: forall k m, k \in (domain m) -> exists v, get m k = Some v.
  Axiom domain_put: forall k v m, domain (put m k v) = union (domain m) (singleton_set k).
  *)
  Axiom reverse_get: map K V -> V -> option K.
  Axiom intersect_map: map K V -> map K V -> map K V.
End TODO.

Local Notation "'bind_opt' x <- a ; f" :=
  (match a with
   | Some x => f
   | None => None
   end)
  (right associativity, at level 70, x pattern).


Section RegAlloc.

  Variable srcvar: Set.
  Context {srcvar_eq_dec: DecidableEq srcvar}.
  Variable impvar: Set.
  Context {impvar_eq_dec: DecidableEq impvar}.
  Variable func: Set.
  Context {func_eq_dec: DecidableEq func}.

  Context {Map: MapFunctions impvar srcvar}.
  Notation srcvars := (@set srcvar (@map_range_set _ _ Map)).
  Notation impvars := (@set impvar (@map_domain_set _ _ Map)).
  Existing Instance map_domain_set.
  Existing Instance map_range_set.

  (* annotated statement: each assignment is annotated with impvar which it assigns,
     loop has map invariant *)
  Inductive astmt: Type :=
    | ASLoad(x: srcvar)(x': impvar)(a: srcvar)
    | ASStore(a: srcvar)(v: srcvar)
    | ASLit(x: srcvar)(x': impvar)(v: Z)
    | ASOp(x: srcvar)(x': impvar)(op: bopname)(y z: srcvar)
    | ASSet(x: srcvar)(x': impvar)(y: srcvar)
    | ASIf(cond: srcvar)(bThen bElse: astmt)
    | ASLoop(inv: map impvar srcvar)(body1: astmt)(cond: srcvar)(body2: astmt)
    | ASSeq(s1 s2: astmt)
    | ASSkip
    | ASCall(binds: list (srcvar * impvar))(f: func)(args: list srcvar).

  Local Notation stmt  := (FlatImp.stmt srcvar func). (* input type *)
  Local Notation stmt' := (FlatImp.stmt impvar func). (* output type *)

  (* impvar -> srcvar mappings which are guaranteed to hold after running s
     (under-approximation) *)
  Definition mappings :=
    fix rec(m: map impvar srcvar)(s: astmt): map impvar srcvar :=
      match s with
      | ASLoad x x' _ | ASLit x x' _ | ASOp x x' _ _ _ | ASSet x x' _ => put m x' x
      | ASStore a v => m
      | ASIf cond s1 s2 => intersect_map (rec m s1) (rec m s2)
      | ASLoop inv s1 cond s2 =>
          (* mi = map if loop was repeated i times *)
          let m0 := rec m s1 in
          let m1 := rec (rec m0 s2) s1 in
          (*
          let m2 := rec (rec m1 s2) s1 in
          let m3 := rec (rec m2 s2) s1 in
          ...
          all further fixpoint iterations will do the same, so m1=m2=m3=...,
          so no need to perform them *)
          intersect_map m0 m1
      | ASSeq s1 s2 => rec (rec m s1) s2
      | ASSkip => m
      | ASCall binds f args => empty_map (* TODO *)
      end.


  Definition checker :=
    fix rec(m: map impvar srcvar)(s: astmt): option (map impvar srcvar * stmt') :=
      match s with
      | ASLoad x x' a =>
          bind_opt a' <- reverse_get m a;
          Some (put m x' x, SLoad x' a')
      | ASStore a v =>
          bind_opt a' <- reverse_get m a;
          bind_opt v' <- reverse_get m v;
          Some (m, SStore a' v')
      | ASLit x x' v =>
          Some (put m x' x, SLit x' v)
      | ASOp x x' op y z =>
          bind_opt y' <- reverse_get m y;
          bind_opt z' <- reverse_get m z;
          Some (put m x' x, SOp x' op y' z')
      | ASSet x x' y =>
          bind_opt y' <- reverse_get m y;
          Some (put m x' x, SSet x' y')
      | ASIf cond s1 s2 =>
          bind_opt cond' <- reverse_get m cond;
          bind_opt (m1, s1') <- rec m s1;
          bind_opt (m2, s2') <- rec m s2;
          Some (intersect_map m1 m2, SIf cond' s1' s2')
      | ASLoop inv s1 cond s2 => None (* TODO need to verify that m implies inv *)
      | ASSeq s1 s2 =>
          bind_opt (m1, s1') <- rec m s1; rec m1 s2
      | ASSkip => Some (m, SSkip)
      | ASCall binds f args => None (* TODO *)
      end.

End RegAlloc.
