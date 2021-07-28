Require Import Rupicola.Lib.Core.
Require Import Rupicola.Lib.IdentParsing.
Require Import Rupicola.Lib.Tactics.

Notation "'let/d' x := val 'in' body" :=
  (dlet val (fun x => body))
    (at level 200, x ident, body at level 200,
     format "'[hv' 'let/d'  x  :=  val  'in' '//' body ']'").

Notation "'let/d' f a0 .. an := val 'in' body" :=
  (dlet (fun a0 => .. (fun an => val) ..) (fun f => body))
    (at level 200, f ident, a0 binder, an binder, body at level 200,
     format "'[hv' 'let/d'  f  a0  ..  an  :=  val  'in' '//' body ']'").

(* TODO: figure out recursive notation for this *)
Notation
      "'let/d' '''(' x , y ')' := val 'in' body" :=
  (dlet val
        (fun v =>
           let x := fst v in
           let y := snd v in
           body))
    (at level 200, only parsing).
Notation
      "'let/d' '''(' x , y , z ')' := val 'in' body" :=
  (dlet val
        (fun v =>
           let x := fst (fst v) in
           let y := snd (fst v) in
           let z := snd v in
           body))
    (at level 200, only parsing).

Notation nlet_eq_k P v :=
  (forall x, x = v -> P x).

Section BlockedLets.
  Definition nlet_eq {A} {P: forall a: A, Type}
             (vars: list string) (a0: A)
             (body : forall (a : A) (Heq: a = a0), P a) : P a0 :=
    let x := a0 in body x eq_refl.

  Definition nlet {A T}
             (vars: list string) (a0: A)
             (body : A -> T) : T :=
    let x := a0 in body x.

  Lemma nlet_as_nlet_eq {A T}
        (vars: list string) (val: A)
        (body : A -> T) :
    nlet vars val body =
    nlet_eq (P := fun _ => T) vars val (fun v _ => body v).
  Proof. reflexivity. Qed.
End BlockedLets.

(* FIXME use `x binder` or `x name` instead of `x ident`? *)

(* FIXME Error: Anomaly "Uncaught exception Failure("hd")." until 8.13 *)
(* Notation "'let/n' x := val 'in' body" := *)
(*   (nlet [_] val (fun x => body)) *)
(*     (at level 200, x ident, body at level 200, *)
(*      format "'[hv' 'let/n'  x  :=  val  'in' '//' body ']'", *)
(*      only printing). *)

Notation "'let/n' x 'as' nm := val 'in' body" :=
  (nlet [nm] val (fun x => body))
    (at level 200, x ident, body at level 200,
     format "'[hv' 'let/n'  x  'as'  nm  :=  val  'in' '//' body ']'").

Notation "'let/n' x 'as' nm 'eq:' Heq := val 'in' body" :=
  (nlet_eq [nm] val (fun x Heq => body))
    (at level 200, x ident, body at level 200,
     format "'[hv' 'let/n'  x  'as'  nm  'eq:' Heq  :=  val  'in' '//' body ']'").

Notation "'let/n' x := val 'in' body" :=
  (nlet [IdentParsing.TC.ident_to_string x] val (fun x => body))
    (at level 200, x ident, body at level 200,
     only parsing).

Notation "'let/n' x 'eq:' Heq := val 'in' body" :=
  (nlet_eq [IdentParsing.TC.ident_to_string x] val (fun x Heq => body))
    (at level 200, x ident, body at level 200,
     only parsing).

(* Notation "'let/n' ( x , y ) := val 'in' body" := *)
(*   (nlet [_; _] val (fun '(x, y) => body)) *)
(*     (at level 200, x ident, body at level 200, *)
(*      format "'[hv' 'let/n'  ( x ,  y )  :=  val  'in' '//' body ']'", *)
(*      only printing). *)

Notation "'let/n' ( x , y ) 'as' ( nx , ny ) := val 'in' body" :=
  (nlet [nx; ny] val (fun xy => let (x, y) := xy in body))
    (at level 200, x ident, body at level 200,
     format "'[hv' 'let/n'  ( x ,  y )  'as'  ( nx ,  ny )  :=  val  'in' '//' body ']'").

Notation "'let/n' ( x , y ) 'as' ( nx , ny ) 'eq:' Heq := val 'in' body" :=
  (nlet [nx; ny] val (fun xy Heq => let (x, y) := xy in body))
    (at level 200, x ident, body at level 200,
     format "'[hv' 'let/n'  ( x ,  y )  'as'  ( nx ,  ny )  'eq:' Heq  :=  val  'in' '//' body ']'").

Notation "'let/n' ( x , y ) 'eq:' Heq := val 'in' body" :=
  (nlet_eq [IdentParsing.TC.ident_to_string x;
           IdentParsing.TC.ident_to_string y]
           val (fun xy Heq => let (x, y) := xy in body))
    (at level 200, x ident, y ident, body at level 200,
     only parsing).

Notation "'let/n' ( x , y ) := val 'in' body" :=
  (nlet [IdentParsing.TC.ident_to_string x;
        IdentParsing.TC.ident_to_string y]
        val (fun xy => let (x, y) := xy in body))
    (at level 200, x ident, y ident, body at level 200,
     only parsing).

Infix "~>" := scalar (at level 40, only parsing).

Notation "[[ locals ]]" := ({| value := locals; _value_ok := _ |}) (only printing).

Declare Scope old.
Delimit Scope old with old.
Notation "'find' body 'implementing' spec 'and-returning' retvars 'and-locals-post' locals_post 'with-locals' locals 'and-memory' mem 'and-trace' tr 'and-rest' R 'and-functions' fns" :=
  (WeakestPrecondition.cmd
     (WeakestPrecondition.call fns)
     body tr mem locals
     (postcondition_cmd locals_post spec retvars R tr)) (at level 0, only parsing).

Notation "<{ 'Trace' := tr ; 'Memory' := mem ; 'Locals' := locals ; 'Functions' := functions }> cmd <{ post }>" :=
  (WeakestPrecondition.cmd
     (WeakestPrecondition.call functions)
     cmd tr mem locals post)
    (at level 0,
     format "'[v' <{  '[v' 'Trace'  :=  '[hv' tr ']' ; '//' 'Memory'  :=  '[hv' mem ']' ; '//' 'Locals'  :=  '[hv' locals ']' ; '//' 'Functions'  :=  '[hv' functions ']' ']'  }> '//' cmd '//' <{  '[hv' post ']'  }> ']'").

Notation "'liftexists' x .. y ',' P" :=
  (Lift1Prop.ex1
     (fun x =>
        ..
          (Lift1Prop.ex1
             (fun y => P)) .. ))
    (x binder, y binder, only parsing, at level 199).

(* precondition is more permissively handled than postcondition in order to
   non-separation-logic (or multiple separation-logic) preconditions *)
Notation "'forall!' x .. y ',' pre '===>' fname '@' args 'returns' rets '===>' post" :=
(fun functions =>
   (forall x,
       .. (forall y,
              forall R tr mem,
                pre R mem ->
                WeakestPrecondition.call
                  functions fname tr mem args
                  (postcondition_func (fun rets => post) R tr)) ..))
     (x binder, y binder, only parsing, at level 199) : old.

Example spec_example_withrets {semantics : Semantics.parameters}
  : spec_of "example" :=
  (forall! (pa : address) (a b : word),
      (sep (pa ~> a))
        ===>
        "example" @ [pa; b] returns r
        ===>
        (liftexists x, emp (r = [x]) * (pa ~> x))%sep)%old.
Example spec_example_norets {semantics : Semantics.parameters}
  : spec_of "example" :=
     (forall! (pa : address) (a b : word),
         (sep (pa ~> a))
           ===>
           "example" @ [pa; b] returns r
           ===>
           (emp (r = []) * (pa ~> word.add a b))%sep)%old.

(* shorthand for no return values *)
Notation "'forall!' x .. y ',' pre '===>' fname '@' args '===>' post" :=
(fun functions =>
   (forall x,
       .. (forall y,
              forall R tr mem,
                pre R mem ->
                WeakestPrecondition.call
                  functions fname tr mem args
                  (postcondition_func_norets post R tr)) ..))
     (x binder, y binder, only parsing, at level 199) : old.

(* N.B. postconditions with no return values still need to take in an argument
   for return values to make types line up. However, the shorthand notation inserts
   a clause to the postcondition saying the return values are nil, so the
   postcondition does not need to ensure this. *)
Example spec_example_norets_short {semantics : Semantics.parameters}
  : spec_of "example" :=
  (forall! (pa : address) (a b : word),
      (sep (pa ~> a))
        ===>
        "example" @ [pa; b]
        ===>
        (fun _ => pa ~> word.add a b)%sep)%old.

Global Open Scope old.

(* unify short and long notations for functions without return values (fails if
   spec_example_norets and spec_example_norets_short are not equivalent) *)
Compute (let x := ltac:(unify @spec_example_norets @spec_example_norets_short) in x).

Infix "⋆" := sep (at level 40, left associativity).

Notation "'fnspec!' name a0 .. an '/' g0 .. gn '~>' r0 .. rn ',' '{' 'requires' functions tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (forall a0,
        .. (forall an,
              (forall g0,
                  .. (forall gn,
                         (forall tr mem,
                             pre%Z ->
                             WeakestPrecondition.call
                               functions name tr mem (cons a0 .. (cons an nil) ..)
                               (fun tr' mem' rets =>
                                  (exists r0,
                                      .. (exists rn,
                                             rets = (cons r0 .. (cons rn nil) ..) /\
                                             post%Z) ..)))) ..)) ..))
    (at level 200,
     name at level 0,
     functions binder,
     a0 binder, an binder,
     g0 binder, gn binder,
     r0 closed binder, rn closed binder,
     tr ident, tr' ident, mem ident, mem' ident,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name a0 .. an '/' g0 .. gn ',' '{' 'requires' functions tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (forall a0,
        .. (forall an,
              (forall g0,
                  .. (forall gn,
                         (forall tr mem,
                             pre%Z%sep ->
                             WeakestPrecondition.call
                               functions name tr mem (cons a0 .. (cons an nil) ..)
                               (fun tr' mem' rets =>
                                  rets = @nil word /\ post%Z%sep))) ..)) ..))
    (at level 200,
     name at level 0,
     functions binder,
     a0 binder, an binder,
     g0 binder, gn binder,
     tr ident, tr' ident, mem ident, mem' ident,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name a0 .. an '~>' r0 .. rn ',' '{' 'requires' functions tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (forall a0,
        .. (forall an,
               (forall tr mem,
                   pre%Z ->
                   WeakestPrecondition.call
                     functions name tr mem (cons a0 .. (cons an nil) ..)
                     (fun tr' mem' rets =>
                        (exists r0,
                            .. (exists rn,
                                   rets = (cons r0 .. (cons rn nil) ..) /\
                                   post%Z) ..)))) ..))
    (at level 200,
     name at level 0,
     functions binder,
     a0 binder, an binder,
     r0 closed binder, rn closed binder,
     tr ident, tr' ident, mem ident, mem' ident,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name a0 .. an ',' '{' 'requires' functions tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (forall a0,
        .. (forall an,
               (forall tr mem,
                   pre%Z%sep ->
                   WeakestPrecondition.call
                     functions name tr mem (cons a0 .. (cons an nil) ..)
                     (fun tr' mem' rets =>
                        rets = @nil word /\ post%Z%sep))) ..))
    (at level 200,
     name at level 0,
     functions binder,
     a0 binder, an binder,
     tr ident, tr' ident, mem ident, mem' ident,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name a0 .. an '/' g0 .. gn ',' '{' 'requires' functions tr mem := pre ';' 'ensures' tr' mem' rets ':=' post '}'" :=
  (fun functions =>
     (forall a0,
        .. (forall an,
              (forall g0,
                  .. (forall gn,
                         (forall tr mem,
                             pre%Z ->
                             WeakestPrecondition.call
                               functions name tr mem (cons a0 .. (cons an nil) ..)
                               (fun tr' mem' rets => post%Z))) ..)) ..))
    (at level 200,
     name at level 0,
     functions binder,
     a0 binder, an binder,
     g0 binder, gn binder,
     tr ident, tr' ident, mem ident, mem' ident,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name a0 .. an ',' '{' 'requires' functions tr mem := pre ';' 'ensures' tr' mem' rets ':=' post '}'" :=
  (fun functions =>
     (forall a0,
        .. (forall an,
               (forall tr mem,
                   pre%Z ->
                   WeakestPrecondition.call
                     functions name tr mem (cons a0 .. (cons an nil) ..)
                     (fun tr' mem' rets => post%Z))) ..))
    (at level 200,
     name at level 0,
     functions binder,
     a0 binder, an binder,
     tr ident, tr' ident, mem ident, mem' ident,
     pre at level 200,
     post at level 200).

Declare Custom Entry defn_spec.

Notation "name '(' a0 , .. , an ')'  '~>'  r0 , .. , rn  {  body  } ,  'implements'  fn" :=
  (name, (cons a0 .. (cons an []) ..), (cons r0 .. (cons rn []) ..),
   match body return cmd with body => body end, fn)
    (in custom defn_spec at level 10,
        name constr at level 0,
        a0 constr at level 0, an constr at level 0,
        r0 constr at level 0, rn constr at level 0,
        body constr at level 200,
        fn constr at level 0,
        no associativity).

Notation "name '(' a0 , .. , an ')'  {  body  } ,  'implements'  fn" :=
  (name, (cons a0 .. (cons an []) ..), (@nil string),
   match body return cmd with body => body end, fn)
    (in custom defn_spec at level 10,
        name constr at level 0,
        a0 constr at level 0, an constr at level 0,
        body constr at level 200,
        fn constr at level 0,
        no associativity).

Notation "defn! spec" :=
  (match spec with
   | spec_constr =>
     (* This match typechecks `spec` before passing it to Ltac, yielding much
        better error messages when `spec` isn't a valid term. *)
     ltac:(lazymatch (eval red in spec_constr) with
           | (?name, ?args, ?rets, ?body, ?gallina) =>
             let proc := constr:((name, (args, rets, body))) in
             let goal := Rupicola.Lib.Tactics.program_logic_goal_for_function
                           proc (@List.nil string) in
             exact (__rupicola_program_marker gallina -> goal)
           end)
   end)
    (at level 0, spec custom defn_spec at level 200, only parsing).
