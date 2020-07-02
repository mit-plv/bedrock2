Require Import Rupicola.Lib.Core.
Require Import Rupicola.Lib.IdentParsing.

Notation "'let/d'  x  :=  val  'in'  body" :=
  (dlet val (fun x => body)) (at level 4).

Definition nlet {A P} (var: string) (val : A) (body : forall a : A, P a) : P val :=
  let x := val in body x.

Notation "'let/n' x 'as' nm := val 'in' body" :=
  (nlet nm val (fun x => body))
    (at level 200, x ident, body at level 200,
     format "'let/n'  x  'as'  nm  :=  val  'in' '//' body",
     only printing).

Notation "'let/n' x := val 'in' body" :=
  (nlet (binder_to_string val x) val (fun x => body))
    (at level 200, x ident, body at level 200,
     only parsing).

Check (let/n x := 1 in let/n x := x + 1 in x).

(* TODO: figure out recursive notation for this *)
Notation
      "'let/d' '''(' x , y ')' := val 'in' body" :=
  (dlet val
        (fun v =>
           let x := fst v in
           let y := snd v in
           body))
    (at level 4, only parsing).
Notation
      "'let/d' '''(' x , y , z ')' := val 'in' body" :=
  (dlet val
        (fun v =>
           let x := fst (fst v) in
           let y := snd (fst v) in
           let z := snd v in
           body))
    (at level 4, only parsing).

Infix "~>" := scalar (at level 40, only parsing).

Notation "[[ locals ]]" := ({| value := locals; _value_ok := _ |}) (only printing).

Definition postcondition_func
           {semantics : Semantics.parameters} spec R tr :=
  (fun (tr' : Semantics.trace) (mem' : Semantics.mem) (rets : list address) =>
     tr = tr'
     /\ sep (spec rets) R mem').

Definition postcondition_func_norets
           {semantics : Semantics.parameters} spec R tr :=
  postcondition_func (fun r => sep (emp (r = nil)) (spec r)) R tr.

(* TODO: see if all uses of locals_post can be rephrased using retvars *)
Definition postcondition_cmd
           {semantics : Semantics.parameters}
           locals_post spec retvars R tr :=
  (fun (tr' : Semantics.trace) (mem' : Semantics.mem)
       (locals : Semantics.locals) =>
     tr = tr'
     /\ locals_post locals
     /\ exists rets,
         map.getmany_of_list locals retvars = Some rets
         /\ sep (spec rets) R mem').

Notation "'find' body 'implementing' spec 'and-returning' retvars 'and-locals-post' locals_post 'with-locals' locals 'and-memory' mem 'and-trace' tr 'and-rest' R 'and-functions' fns" :=
  (WeakestPrecondition.cmd
     (WeakestPrecondition.call fns)
     body tr mem locals
     (postcondition_cmd locals_post spec retvars R tr)) (at level 0).

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
     (x binder, y binder, only parsing, at level 199).
(* test for spec notation *)
Check
  (fun (semantics : Semantics.parameters) =>
     (forall! (pa : address) (a b : word),
         (sep (pa ~> a))
           ===>
           "example" @ [pa; b] returns r
           ===>
           (liftexists x, emp (r = [x]) * (pa ~> x))%sep)).
(* test for spec notation *)
Check
  (fun (semantics : Semantics.parameters) =>
     (forall! (pa : address) (a b : word),
         (sep (pa ~> a))
           ===>
           "example" @ [pa; b] returns r
           ===>
           (emp (r = []) * (pa ~> word.add a b))%sep)).

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
     (x binder, y binder, only parsing, at level 199).
(* test for spec notation *)
Check
  (fun (semantics : Semantics.parameters) =>
     (forall! (pa : address) (a b : word),
         (sep (pa ~> a))
           ===>
           "example" @ [pa; b]
           ===>
           (fun _ => emp True)%sep)).
