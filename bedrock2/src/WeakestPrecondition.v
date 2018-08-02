Require Import bedrock2.Macros bedrock2.Syntax bedrock2.Map.
Require Import Coq.ZArith.BinIntDef.

(* TODO: move? *)
Local Notation "' x <- a | y ; f" :=
  (match a with
   | x => f
   | _ => y
   end)
  (right associativity, at level 70, x pattern).

(* TODO: move? *)
Module Semantics.
  Class parameters := {
    syntax :> Syntax.parameters;

    word : Type;
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
  Section Semantics.
  Context {pp : unique! parameters}.

  Fixpoint load (sz : nat) (m:mem) (a:word) : option word :=
    match sz with
    | O => Some word_zero
    | S sz =>
      'Some b <- map.get m a             | None;
      'Some w <- load sz m (word_succ a) | None;
       Some (combine sz b w)
    end.
  Fixpoint store (sz : nat) (m:mem) (a v:word) : option mem :=
    match sz with
    | O => Some m
    | S sz =>
      let '(b, w) := split sz v in
      'Some _ <- map.get m a | None;
      store sz (map.put m a b) (word_succ a) w
    end.
  Definition trace := list ((mem * actname * list word) * (mem * list word)).
End Semantics. End Semantics.

Module wp. Section wp.
  Local Notation "'bind_ex' x <- a ; f" :=
    (subst! a for a' in exists x, a' x /\ f)
    (only parsing, right associativity, at level 60, f at level 200).
  Local Notation "'bind_ex_Some' x <- a ; f" :=
    (subst! a for a' in exists x, a' = Some x /\ f)
    (only parsing, right associativity, at level 60, f at level 200).
  Local Notation "'bind_eq' x <- a ; f" :=
    (subst! a for a' in forall x, x = a' -> f)
    (only parsing, right associativity, at level 60, f at level 200).

  Import Semantics.
  Context {p : unique! Semantics.parameters}.
  Context (rely guarantee : trace -> Prop) (progress : trace -> trace -> Prop).

  Definition get (l : locals) (x : varname) (v : word) : Prop :=
    map.get l x = Some v.

  Section WithMemAndLocals.
    Context (m : mem) (l : locals).
    Fixpoint expr (e : Syntax.expr) (v : word) : Prop :=
      match e with
      | expr.literal v' => word_of_Z v' = Some v
      | expr.var x => get l x v
      | expr.op op e1 e2 =>
        bind_ex v1 <- expr e1;
        bind_ex v2 <- expr e2;
        interp_binop op v1 v2 = v
      | expr.load s e =>
        bind_ex a <- expr e;
        load (Z.to_nat s) m a = Some v
    end.
  End WithMemAndLocals.

  Section WithF.
    Context {A B} (f: A -> B -> Prop).
    Fixpoint list_map (xs : list A) (ys : list B) {struct xs} : Prop :=
      match xs with
      | nil => ys = nil
      | cons x xs' =>
        bind_ex y <- f x;
          exists ys', ys = cons y ys' /\
                      list_map xs' ys'
      end.
  End WithF.

  Section WithFunctions.
    Context (call : funname -> trace -> mem -> list word -> (trace -> mem -> list word -> Prop) -> Prop).
    Fixpoint cmd (c : cmd) (t : trace) (m : mem) (l : locals)
             (post : trace -> mem -> locals -> Prop) {struct c} : Prop :=
      match c with
      | cmd.skip => post t m l
      | cmd.set x ev =>
        bind_ex v <- expr m l ev;
        bind_eq l <- map.put l x v;
        post t m l
      | cmd.store sz ea ev =>
        bind_ex a <- expr m l ea;
        bind_ex v <- expr m l ev;
        bind_ex_Some m <- store (Z.to_nat sz) m a v;
        post t m l
      | cmd.cond br ct cf =>
        bind_ex v <- expr m l br; (* path-blasting... :( *)
        (word_test v = true  -> cmd ct t m l post) /\
        (word_test v = false -> cmd cf t m l post)
      | cmd.seq c1 c2 =>
        cmd c1 t m l (fun t m l => cmd c2 t m l post)
      | cmd.while e c =>
        exists measure (lt:measure->measure->Prop) (inv:measure->trace->mem->locals->Prop), 
        Coq.Init.Wf.well_founded lt /\
        (exists v, inv v t m l) /\
        (forall v t m l, inv v t m l ->
          exists b, expr m l e b /\
          (word_test b = true -> cmd c t m l (fun t' m l =>
            exists v', inv v' t' m l /\ (progress t' t \/ lt v' v))) /\
          (word_test b = false -> post t m l))
      | cmd.call binds fname arges =>
        bind_ex args <- list_map (expr m l) arges;
        call fname t m args (fun t m rets =>
          bind_ex_Some l <- map.putmany binds rets l;
          post t m l)
      | cmd.interact binds action arges =>
        bind_ex args <- list_map (expr m l) arges;
        let output := (m, action, args) in
        forall m rets (t := cons (output, (m, rets)) t),
          guarantee t /\
          rely t -> (bind_ex_Some l <- map.putmany binds rets l; post t m l)   
      end.
  End WithFunctions.

  Fixpoint call (functions : list (funname * (list varname * list varname * cmd.cmd)))
                (fname : funname) (t : trace) (m : mem) (args : list word)
                (post : trace -> mem -> list word -> Prop) {struct functions} : Prop :=
    match functions with
    | nil => False
    | cons (f, (innames, outnames, c)) functions =>
      'true <- funname_eqb f fname | call functions fname t m args post;
      bind_ex_Some l <- map.putmany innames args map.empty;
      cmd (call functions) c t m l (fun t m l =>
        bind_ex rets <- list_map (get l) outnames;
        post t m rets)
    end.

  Definition program funcs c t m l post : Prop := cmd (call funcs) c t m l post.
End wp. End wp.