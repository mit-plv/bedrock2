Require Import coqutil.sanity coqutil.Macros.subst coqutil.Macros.unique.
Require Import coqutil.Datatypes.PrimitivePair coqutil.Datatypes.HList.
Require Import bedrock2.Notations bedrock2.Syntax coqutil.Map.Interface.
Require Import BinIntDef coqutil.Word.Interface.

Require Coq.Lists.List.

Class parameters := {
  syntax :> Syntax.parameters;

  width : Z;
  word :> Word.Interface.word width;
  byte :> Word.Interface.word 8%Z;

  mem :> map.map word byte;
  locals :> map.map varname word;

  interp_binop : bopname -> word -> word -> word;

  bytes_per : access_size -> nat;
  combine : forall sz, tuple byte (bytes_per sz) -> word;
  split : forall sz, word -> tuple byte (bytes_per sz);

  funname_eqb : funname -> funname -> bool
}.

Section semantics.
  Context {pp : unique! parameters}.
  
  Section WithMem.
    Context (m:mem).
    Fixpoint load_bytes (n : nat) (a : word) {struct n} : option (tuple byte n) :=
      match n with
      | O => Some tt
      | S n =>
        'Some b <- map.get m a | None;
        'Some bs <- load_bytes n (word.add (word.of_Z 1%Z) a) | None;
        Some (pair.mk b bs)
      end.
  End WithMem.
  Definition load m a sz : option word :=
    'Some bs <- load_bytes m (bytes_per sz) a | None;
    Some (combine sz bs).
  Fixpoint store_bytes (n : nat) (m:mem) (a : word) : forall (bs : tuple byte n), mem :=
    match n with
    | O => fun bs => m
    | S n => fun bs => store_bytes n (map.put m a (pair._1 bs)) (word.add (word.of_Z 1%Z) a) (pair._2 bs)
    end.
  Definition store sz m a v : option mem :=
    'Some _ <- load m a sz | None;
    Some (store_bytes (bytes_per sz) m a (split sz v)).
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