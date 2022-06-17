(*|
.. default-role:: math

.. role:: m(math)

The traditional process for developing a verified compiler is to define types that model the source (`S`) and target (`T`) languages, and to write a function `f: S → T` that transforms an instance `s` of the source type into an instance `t = f(s)` of the target type, such all behaviors of `t` match existing behaviors of `s` (“refinement”) and sometimes additionally such that all behaviors of `s` can be achieved by `t` (“equivalence”, or “correctness”).

Naturally, *proving* correctness for such a compiler requires a formal understanding of the *semantics* of languages `S` and `T` (that is, a way to give meaning to programs `s ∈ S` and `t ∈ T`, so that it is possible to speak of the behaviors of a program: return values, I/O, resource usage, etc.).  Then the refinement criterion above translates to `σ_T(t) ⊆ σ_S(s)` (where `σ_S(s)` denotes the behaviors of `s` and `σ_T(t)` those of `t`), and the correctness criterion defines a relation `∼` between source and target programs such that `t ∼ s` iff `σ_T(t) = σ_S(s)`.  With that, a compiler `f` is correct iff `f(s) ∼ s` for all `s`.

Relational compilation is a twist on that approach: it turns out that instead of writing the compiler as a monolithic program and separately verifying it, we can break up the compiler's correctness proof into a collection of orthogonal correctness theorems and *use these theorems* to drive a code-generating proof-search process.  It is a Prolog-style “compilers as relations” approach but taken one step further to get “compilers as (constructive) decision procedures”.

Instead of writing our compiler as a function `f: S → T`, we will write the compiler as a (partial) decision procedure: an automated proof-search process for proving theorems of the form `∃\: t.\; σ_T(t) = σ_S(s)`.  In a constructive setting, any proof of that statement must exhibit a witness `t`, which will be the (correct) compiled version of `s`.  (Note that the theorem does not `∀`-quantify `s`, as we want to generate one distinct proof *per input program* — otherwise, with a `∀ s` quantification, the theorem would be equivalent by skolemization to `∃\: f.\; ∀ s, σ_T(f(s)) = σ_S(s)`, which is the same as defining a single compilation function `f`… and precisely what we're trying to avoid.)

The two main benefits of this approach are flexibility and trustworthiness: it provides a very natural and modular way to think of compiler extensions, and it makes it possible to extract shallowly embedded programs without trusting an extraction routine (in contrast, extraction in Coq is trusted).  The main cost?  Completeness: a (total) function always terminates and produces a compiled output; a (partial) proof-search process may loop or fail to produce an output. [#]_

This is not an entirely new idea: variations on this trick have been variously referred to in the literature as *proof-producing compilation*, *certifying compilation*, and, when the source language is shallowly embedded (we will get to that a bit later), *proof-producing extraction*, *certifying extraction*, or *binary extraction*.  I like to call this style of compilation “relational compilation”, and to explain it I like to start from a traditional verified compiler and progressively derive a relational compiler from it.

.. [#] Of course things are not so clear-cut: a compiler may be written as a partial function that sometimes fails to compile input programs, like ill-typed programs in OCaml, programs with too-deep template recursion in C++, programs with too-long lines in Python, etc. — but the extensibility of relational compilers also tends to make them more susceptible to incompleteness, and since they're written in meta-language it is often not easy or even possible to prove their completeness.

~~~~~~~~~~

.. coq:: none
|*)

From Ltac2 Require Ltac2.

From Coq Require Import String.
From Coq Require Import List ZArith Derive.
Import ListNotations.

Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

Implicit Type z : Z.
Implicit Type str : string.

(*|
A step-by-step example
----------------------

.. coq:: none
|*)

Arguments exist [A] {_} _ {_}.
Arguments ex_intro [A] {_} _ {_}.
Notation "'type' 'of' x" := ((fun A (_: A) => A) _ x) (at level 0).
Set Warnings "-deprecated-hint-without-locality".

Tactic Notation "eauto" "with" ident(db) :=
  typeclasses eauto with db.

Module Arith.

(*|
Here is a concrete pair of languages that we will use as a demonstration.  Language `S` is a simple arithmetic-expressions language.  Language `T` is a trivial stack machine.

..
   You can `download the Coq code of this example <relational-compilation.v>`__.

.. default-role:: coq

Language definitions
~~~~~~~~~~~~~~~~~~~~

On the left is the Coq definition of `S`, with only three constructors: constants, negation, and addition; on the right is the definition of `T`: a program in `T` is a list of stack operations `T_Op`, which may be pushing a constant, popping the two values on the top of the stack and pushing their difference, or popping the two values on the top of the stack and pushing their sum.

.. compound::
   :class: sidebyside

   .. container:: narrowside

      .. coq::
|*)

Inductive S :=
| SInt z
| SOpp (s : S)
| SAdd (s1 s2 : S).
Implicit Type s : S. (* .none *)

(*|
      .. coq:: none
|*)

(*
Notation "$ z" := (SInt z) (at level 34, format "$ z").
Notation "$- z" := (SOpp z) (at level 35, format "$- z").
Infix "$+" := SAdd (at level 50, left associativity).
*)

(*|
   .. container:: wideside

      .. coq::
|*)

Inductive T_Op :=
| TPush z
| TPopSub
| TPopAdd.
Implicit Type op : T_Op. (* .none *)

Definition T := list T_Op.
Implicit Type t : T. (* .none *)

(*|
Concretely, a program in ``S`` might be `SAdd (SInt 3) (SInt 4)`, which computes the sum of the constants `3` and `4`.  A corresponding program in `T` would be `[TPush 3; TPush 4; TPopAdd]`, which pushes the constants `3` and `4` and then places their sum on the stack.

Semantics
~~~~~~~~~
The semantics of these languages are easy to define using interpreters.  On the left, operations on terms in `S` are mapped to corresponding operations on :m:`ℤ`, producing an integer.  On the right, stack operations are interpreted one by one, starting from a stack and producing a new stack.

.. compound::
   :class: sidebyside

   .. container:: narrowside

      .. coq::
|*)

Fixpoint σS s : Z :=
  match s with
  | SInt z     => z
  | SOpp s     => - σS s
  | SAdd s1 s2 => σS s1 + σS s2
  end.

(*|
   .. container:: wideside

      .. coq::
|*)

Notation Stack := (list Z).

Definition σOp (ts: Stack) op : Stack :=
  match op, ts with
  | TPush n, ts => n :: ts
  | TPopAdd, n2::n1::ts => n1+n2 :: ts
  | TPopSub, n2::n1::ts => n1-n2 :: ts
  | _, ts => ts (* Invalid: no-op *)
  end.

Definition σT t (ts: Stack) : Stack :=
  List.fold_left σOp t ts.

(*|
With these definitions, program equivalence is straightforward to define (the definition is contextual, in the sense that it talks about equivalence in the context of a non-empty stack):
|*)

Module DeepEmbedded. (* .none *)
Notation "t ∼ s" := (forall ts, σT t ts = σS s :: ts)
  (at level 70).

(*|
Compilation
~~~~~~~~~~~

In the simplest case, a compiler is a single recursive function; more typically, a compiler is engineered as a sequence (composition) of passes, each responsible for a well-defined task: typically, either an *optimization* (within one language, intended to improve performance of the output) or *lowering* (from one intermediate language to another, intended to bring the program closer to its final form), though these boundaries are porous.  Here is a simple one-step compiler for our pair of languages:
|*)

Fixpoint StoT s := match s with
  | SInt z     => [TPush z]
  | SOpp s     => [TPush 0] ++ StoT s ++ [TPopSub]
  | SAdd s1 s2 => StoT s1 ++ StoT s2 ++ [TPopAdd]
end.

(*|
The `SInt` case maps to a stack-machine program that simply pushes the constant `z` on the stack; the `SOpp` case returns a program that first puts a 0 on the stack, then computes the value corresponding to the operand `s`, and finally computes the subtraction of these two using the `TPopSub` opcode; and the `SAdd` case produces a program that pushes both operands in succession before computing their sum using the `TPopAdd` opcode.

The Coq command ``Compute`` lets us run this compiler and confirm that it seems to operate correctly:
|*)

Example s7 :=
  SAdd (SAdd (SInt 3) (SInt 6))
       (SOpp (SInt 2)).

(*|
- Running the example program `s7` directly
  returns `7`:
|*)

Compute σS s7. (* .unfold *)

(*|
- Compiling the program and then running it produces the same result (a stack with a single element, `7`):

  .. coq::
|*)

Compute StoT s7. (* .unfold *)
Compute σT (StoT s7) []. (* .unfold *)

(*|
Compiler correctness
~~~~~~~~~~~~~~~~~~~~

Of course, one example is not enough to establish that the compiler above works; instead, here is a proof of its correctness, which proceeds by induction with three cases:

.. coq::
   :name: fn-ok
|*)

Lemma StoT_Rok : forall s, StoT s ∼ s.
Proof.
  induction s.
  all: intros; unfold σT; simpl.
  - (* `SInt` case *)
    reflexivity.
  - (* `SOpp` case *)
    rewrite fold_left_app.
    rewrite IHs.
    reflexivity.
  - (* `SAdd` case *)
    rewrite !fold_left_app.
    rewrite IHs1, IHs2.
    reflexivity.
Qed.

(*|
This compiler operates in a single pass, but arguably even a small compiler like this one could benefit from a multi-pass approach: for example, we might prefer to separate lowering into two phases translating all unary `SOpp` operations to a new binary operator `SSub` (`SOpp x → SSub (Sconst 0) x`) in a first pass, and dealing with stack operations in a second pass.

Compiling with relations
~~~~~~~~~~~~~~~~~~~~~~~~

We will observe two things about `StoT` and its proof.

First, `StoT`, like any function, can be rewritten as a relation (any function :m:`f: x ↦ f(x)` defines a relation :m:`∼_f` such that :m:`t ∼_f s` iff :m:`t = f(s)`; this relation is sometimes called the graph of the function).  Here is one natural way to rephrase `StoT` as a relation `ℜ`; notice how each branch of the recursion maps to a case in the inductive definition of the relation (each constructor defines an introduction rule for `ℜ`, which corresponds to a branch in the original recursion, and each `x ℜ y` premise of each case corresponds to a recursive call to the function):
|*)

Reserved Notation "t 'ℜ' s"
  (at level 68, no associativity). (* .none *)
Inductive StoT_rel : T -> S -> Prop :=
| StoT_RNat : forall z,
    [TPush z] ℜ SInt z
| StoT_ROpp : forall t s,
    t ℜ s ->
    [TPush 0] ++ t ++ [TPopSub] ℜ SOpp s
| StoT_RAdd : forall t1 s1 t2 s2,
    t1 ℜ s1 ->
    t2 ℜ s2 ->
    t1 ++ t2 ++ [TPopAdd] ℜ SAdd s1 s2
where "t 'ℜ' s" := (StoT_rel t s).

(*|
Now, what does correctness mean for `StoT`?  Correctness for this compilation relation is… just a subset relation:

   The relation `ℜ` is a *correct* compilation relation for languages :m:`S` and :m:`T` if its graph is a subset of the graph of :m:`∼`.

This condition is sufficient: any relation that is a subset of :m:`∼` defines a correct (possibly one-to-many, possibly suboptimal, but *correct*\ ) mapping from source programs to destination programs.

And indeed, the relation above is a correct compilation relation:

.. coq::
   :name: rel-ok
|*)

Theorem StoT_rel_ok : forall t s,
    t ℜ s -> t ∼ s.
Proof.
  induction 1.
  all: intros; unfold σT; simpl. (* .fold *)
  - (* `StoT_RNat` case *)
    reflexivity.
  - (* `StoT_ROpp` case *)
    rewrite fold_left_app.
    rewrite IHStoT_rel.
    reflexivity.
  - (* `StoT_RAdd` case *)
    rewrite !fold_left_app.
    rewrite IHStoT_rel1, IHStoT_rel2.
    reflexivity.
Qed.

(*|
Now that we have `ℜ`, we can use it to prove equivalences for specific programs: for example, we can write a proof to show specifically that the compiled version of our example program `s7` matches the original `s7` by applying each of the constructors of the relation `ℜ` one by one:
|*)

Goal ([TPush 3] ++ [TPush 6] ++ [TPopAdd]) ++
     ([TPush 0] ++ [TPush 2] ++ [TPopSub]) ++
     [TPopAdd] ℜ
     SAdd (SAdd (SInt 3) (SInt 6))
     (SOpp (SInt 2)).
Proof.
  apply StoT_RAdd. (* .unfold *)
  - apply StoT_RAdd. (* .unfold *)
    + apply StoT_RNat.
    + apply StoT_RNat.
  - apply StoT_ROpp. (* .unfold *)
    + apply StoT_RNat.
Qed.

(*|
Now, how can we use this relation to *run* the compiler instead?  By using proof search!  This is standard practice in the world of logic programming.  To *compile* our earlier program `s7`, for example, we can simply search for a program `t7` such that `t7 ℜ s7`, which in Coq terms looks like this:
|*)

Example t7_rel: { t7 | t7 ℜ s7 }.
Proof.
  unfold s7; eexists. (* .unfold *)

(*|
Now the goal includes an indeterminate value `?t7`, called an existential variable (\ *evar*\ ), corresponding to the program that we are attempting to derive, and each application or a lemma *refines* that evar by plugging in a partial program:
|*)

  apply StoT_RAdd. (* .unfold *)

(*|
After applying the lemma `StoT_RAdd`, we are asked to provide two subprograms, each corresponding to one operand of the addition:
|*)

  - apply StoT_RAdd. (* .unfold *)
    + apply StoT_RNat.
    + apply StoT_RNat.
  - apply StoT_ROpp. (* .unfold *)
    + apply StoT_RNat.
Defined.

(*|
We get the exact same program, but this time instead of *validating* a previous compilation pass, we have generated the program from scratch:
|*)

Compute t7_rel. (* .unfold *)

(*|
We can also use Coq's inspection facilities to see the proof term as it is being generated (this time the boxes show the internal proof term, not the goals):

.. coq:: none
|*)

Goal { t7 | t7 ℜ s7 }. (* .none *)
Proof.
  unfold s7; eexists.

(*|
.. coq:: unfold in
|*)

  Show Proof. (* .messages .no-in *)
  apply StoT_RAdd. (* .in *)
  Show Proof. (* .messages .no-in *)
  - apply StoT_RAdd.
    Show Proof. (* .messages .no-in *)
    + apply StoT_RNat.
      Show Proof. (* .messages .no-in *)
    + apply StoT_RNat.
      Show Proof. (* .messages .no-in *)
  - apply StoT_ROpp.
    Show Proof. (* .messages .no-in *)
    + apply StoT_RNat.
      Show Proof. (* .messages .no-in *)
Defined. (* .none *)

(*|
This derivation shows how the program gets built: each lemma application is equivalent to one recursive call in a run of the compilation function `StoT`.

Coq has facilities to perform proof search automatically using a set of lemmas, which we can use to automate the derivation of `t7`: it suffices to register all constructors of `ℜ` in a “hint database”, as follows: [#]_

.. [#] In the following we use ``eauto`` as an abbreviation for ``typeclasses eauto``, a more flexible version of Coq's ``eauto`` tactic.  In particular, using ``typeclasses eauto`` allows us to specify priorities on lemmas.
|*)

Create HintDb cc.
Hint Resolve exist : cc. (* .none *)
Hint Constructors StoT_rel : cc.

Example t7_rel_eauto: { t7 | t7 ℜ s7 }.
Proof. eauto with cc. Defined.

Compute t7_rel_eauto. (* .unfold *)

(*|
And of course, the result is *correct-by-construction*, in the sense that it carries its own proof of correctness:
|*)

Eval cbn in type of (proj2_sig t7_rel_eauto). (* .unfold *)

(*|
This is traditional *logic programming*, applied to compilers.  We have now learned one fact:

   Correctly compiling a program :m:`s` is the same as proving :m:`∃\: t.\; t ∼ s`.

Open-ended compilation
~~~~~~~~~~~~~~~~~~~~~~

The proofs of correctness for the functional version of the compiler (`StoT`, :mref:`.io#fn-ok.s(Proof)`) and for the relational version (`StoT_rel`, :mref:`.io#rel-ok.s(Proof)`) have the exact same structure.  They are both composed of three orthogonal lemmas:

.. class:: tight-list

1. .. mquote:: .io#rel-ok.s(induction).g#1.ccl
2. .. mquote:: .io#rel-ok.s(induction).g#2.ccl
3. .. mquote:: .io#rel-ok.s(induction).g#3.ccl

Each of these is really a standalone fact, and each corresponds to a *partial* relation between :m:`S` and :m:`T`, each connecting *some* programs in :m:`S` to *some* programs in :m:`T`.  In other words:

   A relational compiler is really just a collection of facts connecting programs in the target language to programs in the source language.

This means that we don't even need to define a relation.  Instead, we can have three lemmas that directly refer to the original equivalence `~`:
|*)

Lemma StoT_Int z :
    [TPush z] ∼ SInt z.

(*|
.. coq:: none
|*)

Proof. reflexivity. Qed.

(*||*)

Lemma StoT_Opp t s :
    t ∼ s ->
    [TPush 0] ++ t ++ [TPopSub] ∼ SOpp s.

(*|
.. coq:: none
|*)

Proof.
  unfold σT; simpl; intros * IH *.
  rewrite fold_left_app, IH.
  reflexivity.
Qed.

(*||*)

Lemma StoT_Plus t1 s1 t2 s2 :
    t1 ∼ s1 ->
    t2 ∼ s2 ->
    t1 ++ t2 ++ [TPopAdd] ∼ SAdd s1 s2.

(*|
.. coq:: none
|*)

Proof.
  unfold σT; simpl; intros * IH1 IH2 *.
  rewrite !fold_left_app, IH1, IH2.
  reflexivity.
Qed.

(*|
And from these, we can build a compiler!  We just need to place all these facts into a new database of lemmas, which Coq will use as part of its proof search:
|*)

Create HintDb c.
Opaque σS σT.
Hint Resolve exist : c. (* .none *)
Hint Resolve StoT_Int : c.
Hint Resolve StoT_Opp : c.
Hint Resolve StoT_Plus : c.

(*|
And then we can derive compiled programs and their proofs:
|*)

Example t7_fn_eauto: { t7 | t7 ∼ s7 }.
Proof. eauto with c. Defined.

Compute t7_fn_eauto. (* .unfold *)

(*|
.. sidebar:: _`Box 1` — Opacity

   Making `σS` and `σT` *opaque* prevents commands like ``eauto`` from unfolding our definitions too aggressively.  Without it, since our example language :m:`S` is so simple that all programs are actually just constants (!), our new compiler would just reduce programs before compiling them:
|*)

Transparent σS σT.
Example t7_fn_eauto_t: { t7 | t7 ∼ s7 }. Proof. eauto with c. Defined.
Compute t7_fn_eauto_t. (* .unfold *)
End DeepEmbedded. (* .none *)

(*|
   The alternative would be to give priority to `StoT_Opp` and `StoT_Plus` over `StoT_int`, which we demonstrate later in this document.

   .. massert::

      .s(Compute).msg{*TPush 7*}

That is the core idea of relational compilation.  On this simple example it looks mostly like an odd curiosity, but it is actually very useful for compiling (shallowly) embedded domain-specific languages (EDSLs), especially when the compiler needs to be extensible.

Use case 1: Compiling shallowly embedded DSLs
---------------------------------------------

.. coq:: none
|*)

Module ShallowEmbedded.

(*|
The original setup of the problem (compiling from language :m:`S` to language :m:`T`) required us to exhibit a function :m:`f: S → T`.  Not so with the new set up, which instead requires us to prove instances of the `∼` relation (one per program).  What this means is that we can apply this compilation technique to compile *shallowly* embedded programs, including shallowly embedded DSLs [#]_.

.. [#] A shallow embedding is one where programs are defined directly in the host language in contrast with a deep embedding where programs are represented as abstract syntax trees, i.e. data.

Here is how we would change our previous example to compile arithmetic expressions written directly in Gallina:

1. Start by redefining the relation to use *Gallina expressions* on the right side of the equivalence (there are no more references to :m:`S` nor ``σS``):

   .. coq::
|*)

Notation "t ≈ s" := (forall ts, σT t ts = s :: ts) (at level 68).

(*|
2. Add compilation lemmas (the proofs are exactly the same as before, so they are omitted).  Note that on the right side we have plain Gallina `+` and `-`, not `SAdd` and `SOp`, so each lemma now relates a shallow program to an equivalent deep-embedded one:

   .. coq::
|*)

Lemma GallinatoT_Z z :
  [TPush z] ≈ z.

(*|
   .. coq:: none
|*)

Proof. reflexivity. Qed.

(*||*)

Lemma GallinatoT_Zopp t z :
  t ≈ z ->
  [TPush 0] ++ t ++ [TPopSub] ≈ - z.

(*|
   .. coq:: none
|*)

Proof.
  unfold σT; simpl; intros * IH *.
  rewrite fold_left_app, IH.
  reflexivity.
Qed.

(*||*)

Lemma GallinatoT_Zadd t1 z1 t2 z2 :
  t1 ≈ z1 ->
  t2 ≈ z2 ->
  t1 ++ t2 ++ [TPopAdd] ≈ z1 + z2.

(*|
   .. coq:: none
|*)

Proof.
  unfold σT; simpl; intros * IH1 IH2 *.
  rewrite !fold_left_app, IH1, IH2.
  reflexivity.
Qed.

(*|
These lemmas are sufficient to create a small compiler: as before we populate a hint database with our compilation lemmas:
|*)

Create HintDb stack.
Hint Opaque Z.add Z.opp : stack. (* .none *)
Hint Resolve exist : stack. (* .none *)
Hint Resolve GallinatoT_Z | 10 : stack.
Hint Resolve GallinatoT_Zopp : stack.
Hint Resolve GallinatoT_Zadd : stack.

(*|
And then we run our relational compiler on shallowly embedded input programs:
|*)

Example g7 := 3 + 6 + Z.opp 2.

Example t7_shallow: { t7 | t7 ≈ g7 }.
Proof. eauto with stack. Defined.

Compute t7_shallow. (* .unfold *)

(*|
Of course, it is easy to package this process in a convenient notation (the pattern `match Set return T with _ => X end` is a roundabout way to force the type of the value `X`):
|*)

Notation compile gallina_term :=
  (match Set return { t | t ≈ gallina_term } with
   | _ => ltac:(eauto with stack)
   end)
  (only parsing).

Compute compile (3 + 6 + Z.opp 2). (* .unfold *)

(*|
There is something slightly magical happening here.  By rephrasing compilation as a proof search problem, we have been able to construct a compiler that would not even be expressible (let alone provable!) as a regular Gallina function.  Reasoning on shallowly embedded programs is often much nicer than reasoning on deeply embedded programs, and this technique offers a convenient way to bridge the gap.

.. coq:: none
|*)

End ShallowEmbedded.
End Arith.
