Require Import bedrock2.Macros bedrock2.Notations bedrock2.Syntax bedrock2.Map.
Require Import Coq.ZArith.BinIntDef.

Require Coq.Lists.List.

Class parameters := {
  syntax :> Syntax.parameters;

  word : Set;
  word_zero : word;
  word_succ : word -> word;
  word_test : word -> bool;
  word_of_Z : BinNums.Z -> option word;
  interp_binop : bopname -> word -> word -> word;

  byte : Type;
  (* nat included for conceptual completeness, only middle-endian would use it *)
  combine : nat -> byte -> word -> word;
  split : nat -> word -> byte * word;

  mem :> map word byte;
  locals :> map varname word;

  funname_eqb : funname -> funname -> bool
}.

Section semantics.
  Context {pp : unique! parameters}.
  
  Fixpoint load_rec (sz : nat) (m:mem) (a:word) : option word :=
    match sz with
    | O => Some word_zero
    | S sz =>
      'Some b <- map.get m a                 | None;
      'Some w <- load_rec sz m (word_succ a) | None;
       Some (combine sz b w)
    end.
  Definition load n := load_rec (Z.to_nat n).
  Fixpoint unchecked_store_rec (sz : nat) (m:mem) (a v:word) : mem :=
    match sz with
    | O => m
    | S sz =>
      let '(b, w) := split sz v in
      unchecked_store_rec sz (map.put m a b) (word_succ a) w
    end.
  Definition unchecked_store n := unchecked_store_rec (Z.to_nat n).
  Definition store sz m a v : option mem :=
    match load sz m a with
    | None => None
    | Some _ => Some (unchecked_store sz m a v)
    end.
  Definition trace := list ((mem * actname * list word) * (mem * list word)).

  Context (eval : locals -> expr -> word -> Prop).
  Context (rely guarantee : trace -> Prop) (progress : trace -> trace -> Prop).
  Implicit Types post : trace -> mem -> locals -> Prop. (* COQBUG(unification finds Type instead of Prop and fails to downgrade *)

  Print cmd.cmd.
  Inductive exec
    : cmd
    -> trace -> mem -> locals
    -> (trace -> mem -> locals -> Prop)
    -> Prop :=
  | skip t m l post (_:post t m l)
    : exec cmd.skip t m l post
  | set x e t m l post
        v (_ : eval l e v)
        (_ : post t m (map.put l x v))
    : exec (cmd.set x e) t m l post
  | seq c1 c2 t m l post
        mid (_ : exec c1 t m l mid)
        (_ : forall t m l, exec c2 t m l post)
    : exec (cmd.seq c1 c2) t m l post
  | while e c t m l post
          v (_ : eval l e v)
          (_ : Logic.or
                 (word_test v = false /\ post t m l)
                 (word_test v = true /\ exec (cmd.seq c (cmd.while e c)) t m l post))
    : exec (cmd.while e c) t m l post
  | interact bindvars action arges t m l post
             args (_ : List.Forall2 (eval l) arges args)
             (output := (m, action, args))
             (_ : forall m rets (t := cons (output, (m, rets)) t),
                 guarantee t /\
                 rely t -> (bind_ex_Some l <- map.putmany bindvars rets l; post t m l))
    : exec (cmd.interact bindvars action arges) t m l post
           (*
  | call
      env (* FIXME : move above *)
      bindvars fname arges t m l post
      args (_ : List.Forall2 (eval l) arges args)
      params c retvars (_ : map.get env fname = Some (params, c, retvars))
      l0 (_ : map.putmany params args map.empty = Some l0)
      beforeret (_ : exec c t m l0 beforeret)
      (_ : forall t' m' l', beforeret t' m' l' ->
                            exists rets, List.Forall2 (fun x v => map.get l' x = Some v) retvars rets /\
                            exists l'', map.putmany bindvars rets l = Some l'' /\
                            post t' m' l'')
    : exec (cmd.call bindvars fname arges) t m l post
*)
  .
End semantics.