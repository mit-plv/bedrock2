Require Import Rupicola.Lib.Api.

Section with_parameters.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok _}.
  Definition example (x: word) (y: word) :=
    let/n x := word.and (word.add y (word.of_Z 1))
                       (word.xor (word.add (word.sub x y) x)
                                 (word.of_Z 0)) in
    x.

  Implicit Type R : Semantics.mem -> Prop.
  Instance spec_of_example : spec_of "example" :=
    fnspec! "example" (x y: word) ~> z,
    { requires fns tr mem := True;
      ensures tr' mem' :=
        tr = tr' /\
        mem = mem' /\
        z = example x y }.

  Derive example_body SuchThat
         (defn! "example"("x", "y") ~> "x"
              { example_body },
          implements example)
         As example_body_correct.
  Proof.
    compile.
  Qed.

  Open Scope Z_scope.

  Definition exZ (x: Z) (y: Z) :=
    let t := y + x in
    let t1 := (1 - x) * (Z.land y 1) in
    let/n t1 := t1 - (Z.lxor t 1) in
    let t2 := (1 - y) * (y + 3) in
    let/n t2 := Z.lor x (t * 3 + 1) in
    let t3 := t - (Z.lxor t 1) in
    let t3 := (1 - t3) * (y + t3) in
    let/n t3 := Z.lor x (t3 * 3 + 1) in
    let t4 := (Z.land (y + 1) (Z.lxor (t - y + t) 0)) in
    let/n t4 := Z.lor t4 (1 + t4) in
    let t5 := t + (t - 8) in
    let/n x := t1 + t2 - t3 + t4 - t5 in
    x.

  Instance spec_of_exZ : spec_of "exZ" :=
    fnspec! "exZ" (x y: word) ~> z,
    { requires fns tr mem := True;
      ensures tr' mem' :=
        tr = tr' /\
        mem = mem' /\
        z = word.of_Z (exZ (word.unsigned x) (word.unsigned y)) }.

  Derive exZ_body SuchThat
         (defn! "exZ"("x", "y") ~> "x"
              { exZ_body },
          implements exZ)
         As exZ_body_correct.
  Proof.
    compile.
  Qed.

  Compute exZ_body.
End with_parameters.
