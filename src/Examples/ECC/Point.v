Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.ECC.Field.

Section Gallina.
  Definition point : Type := (Z * Z).
End Gallina.

Section Compile.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {field_parameters : FieldParameters}
          {bignum_representation : BignumRepresentation}.

  Lemma compile_point_assign :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr R functions T (pred: T -> _ -> Prop)
      (x y : Z) (X Y : bignum) k k_impl,
      eval X = x ->
      eval Y = y ->
      let v := (x, y) in
      (let head := v in
       find k_impl
            implementing (pred (dlet (eval X)
                                     (fun x => dlet (eval Y)
                                                    (fun y => k (x, y)))))
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (let head := v in
       find k_impl
       implementing (pred (dlet head k))
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    repeat straightline'. subst; auto.
  Qed.
End Compile.
