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
           (locals_ok : Semantics.locals -> Prop)
      tr R functions T (pred: T -> _ -> Prop)
      (x y : Z) (X Y : bignum) k k_impl,
      (eval X mod M = x mod M)%Z ->
      (eval Y mod M = y mod M)%Z ->
      let v := (x mod M, y mod M)%Z in
      (let head := v in
       find k_impl
       implementing (pred (dlet (eval X mod M)%Z
                                (fun x => dlet (eval Y mod M)%Z
                                               (fun y => k (x, y)))))
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (let head := v in
       find k_impl
       implementing (pred (dlet head k))
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    repeat straightline'.
    repeat match goal with
             H : (?x mod M = _ mod M)%Z |- _ =>
             rewrite H in *
           end.
    eauto.
  Qed.
End Compile.
