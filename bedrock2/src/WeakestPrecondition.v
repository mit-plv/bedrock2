Require Import bedrock2.Macros bedrock2.Notations bedrock2.Map.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import Coq.ZArith.BinIntDef.

Section WeakestPrecondition.
  Context {p : unique! Semantics.parameters}.
  Context (rely guarantee : trace -> Prop) (progress : trace -> trace -> Prop).
  Variable resolver : globname -> option word.

  Definition literal v post : Prop :=
    bind_ex_Some v <- word_of_Z v; post v.
  Definition get (l : locals) (x : varname) (post : word -> Prop) : Prop :=
    bind_ex_Some v <- map.get l x; post v.
  Definition load s m a (post : _ -> Prop) : Prop :=
    bind_ex_Some v <- load s m a; post v.
  Definition store sz m a v post :=
    bind_ex_Some m <- store sz m a v; post m.

  Section WithMemAndLocals.
    Context (m : mem) (l : locals).
    Fixpoint expr (e : Syntax.expr) (post : word -> Prop) : Prop :=
      match e with
      | expr.literal v =>
        literal v post
      | expr.var x =>
        get l x post
      | expr.global g =>
        bind_ex_Some v <- resolver g ; post v
      | expr.op op e1 e2 =>
        expr e1 (fun v1 =>
        expr e2 (fun v2 =>
        post (interp_binop op v1 v2)))
      | expr.load s e =>
        expr e (fun a =>
        load s m a post)
    end.
  End WithMemAndLocals.

  Section WithF.
    Context {A B} (f: A -> (B -> Prop) -> Prop).
    Fixpoint list_map (xs : list A) (post : list B -> Prop) {struct xs} : Prop :=
      match xs with
      | nil => post nil
      | cons x xs' =>
        f x (fun y =>
        list_map xs' (fun ys' =>
        post (cons y ys')))
      end.
  End WithF.

  Section WithFunctions.
    Context (call : word -> trace -> mem -> list word -> (trace -> mem -> list word -> Prop) -> Prop).
    Fixpoint cmd (c : cmd) (t : trace) (m : mem) (l : locals)
             (post : trace -> mem -> locals -> Prop) {struct c} : Prop :=
      match c with
      | cmd.skip => post t m l
      | cmd.set x ev =>
        expr m l ev (fun v =>
        bind_eq l <- map.put l x v;
        post t m l)
      | cmd.store sz ea ev =>
        expr m l ea (fun a =>
        expr m l ev (fun v =>
        store sz m a v (fun m =>
        post t m l)))
      | cmd.cond br ct cf =>
        expr m l br (fun v => (* path-blasting... :( *)
        (word_test v = true  -> cmd ct t m l post) /\
        (word_test v = false -> cmd cf t m l post))
      | cmd.seq c1 c2 =>
        cmd c1 t m l (fun t m l => cmd c2 t m l post)
      | cmd.while e c =>
        exists measure (lt:measure->measure->Prop) (inv:measure->trace->mem->locals->Prop),
        Coq.Init.Wf.well_founded lt /\
        (exists v, inv v t m l) /\
        (forall v t m l, inv v t m l ->
          expr m l e (fun b =>
          (word_test b = true -> cmd c t m l (fun t' m l =>
            exists v', inv v' t' m l /\ (progress t' t \/ lt v' v))) /\
          (word_test b = false -> post t m l)))
      | cmd.call binds f arges =>
        list_map (expr m l) arges (fun args =>
        expr m l f (fun fname =>
        call fname t m args (fun t m rets =>
          bind_ex_Some l <- map.putmany binds rets l;
          post t m l)))
      | cmd.interact binds action arges =>
        list_map (expr m l) arges (fun args =>
        let output := (m, action, args) in
        forall m rets (t := cons (output, (m, rets)) t),
          guarantee t /\
          (rely t -> (bind_ex_Some l <- map.putmany binds rets l; post t m l)))
      end.
  End WithFunctions.

  Section list_lookup.
    Context {A B : Type} (eqA : A -> A -> bool) (key : A).
    Fixpoint list_lookup (ls : list (A * B)) : option B :=
      match ls with
      | nil => None
      | cons (key', val) ls =>
        if eqA key key' then Some val
        else list_lookup ls
      end.
  End list_lookup.

  Definition func call '(innames, outnames, c)
             (t : trace) (m : mem) (args : list word)
             (post : trace -> mem -> list word -> Prop) :=
      bind_ex_Some l <- map.putmany innames args map.empty;
      cmd call c t m l (fun t m l =>
        list_map (get l) outnames (fun rets =>
        post t m rets)).

  Section rec.
    Variable (functions : list (word * (list varname * list varname * cmd.cmd))).

    (* This definition allows for recursive functions using step-indexing.
     *
     * note(gmm): using this definition, you would likely write something like:
     * `forall n, func (call_rec (3 + n)) ...` which would allow you to make
     * calls to functions that have a call depth of at most 3.
     * This is equivalent to the previous definition is you use the length
     * of the rest of the list.
     * in general, the `n` could be dependent (relationally or functionally)
     * on both the arguments to the function and the heap.
     *)
    Fixpoint call_rec (n : nat)
             (fname : word) (t : trace) (m : mem) (args : list word)
             (post : trace -> mem -> list word -> Prop) {struct n} : Prop :=
      match n with
      | 0 => False
      | S n =>
        match list_lookup word_eqb fname functions with
        | None => False
        | Some decl => func (call_rec n) decl t m args post
        end
      end.

    (* note(gmm): `call_rec` is monotone in `n` *)

  End rec.

  Fixpoint call
           (functions : list (word * (list varname * list varname * cmd.cmd)))
           (fname : word) (t : trace) (m : mem) (args : list word)
           (post : trace -> mem -> list word -> Prop) {struct functions} : Prop :=
    match functions with
    | nil => False
    | cons (f, decl) functions =>
      if word_eqb f fname
      then func (call functions) decl t m args post
      else call functions fname t m args post
    end.

  Definition program funcs main t m l post : Prop :=
    cmd (call funcs) main t m l post.
End WeakestPrecondition.