Require Import Rupicola.Lib.Core.

Notation "'let/d'  x  :=  val  'in'  body" :=
  (dlet val (fun x => body)) (at level 4).

Infix "~>" := scalar (at level 40, only parsing).

Notation "[[ locals ]]" := ({| value := locals; _value_ok := _ |}) (only printing).

Definition postcondition_for
           {semantics : Semantics.parameters} spec R tr :=
  (fun (tr' : Semantics.trace) (mem' : Semantics.mem) (rets : list address) =>
     tr = tr' /\ rets = nil
     /\ sep spec R mem').

Definition postcondition_norets
           {semantics : Semantics.parameters} spec R tr :=
  (fun (tr' : Semantics.trace) (mem' : Semantics.mem) (_ : Semantics.locals) =>
     postcondition_for spec R tr tr' mem' []).

Notation "'find' body 'implementing' spec 'with-locals' locals 'and-memory' mem 'and-trace' tr 'and-rest' R 'and-functions' fns" :=
  (WeakestPrecondition.cmd
     (WeakestPrecondition.call fns)
     body tr mem locals
     (postcondition_norets spec R tr)) (at level 0).
