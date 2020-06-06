Require Import Rupicola.Lib.Api.
Local Open Scope Z_scope.

Class FieldParameters :=
  { (** mathematical parameters **)
    M : Z; (* modulus *)
    a24 : Z; (* (a+2) / 4 or (a-2) / 4, depending on the implementation *)
    Finv : Z -> Z; (* modular inverse in Z/M *)
    (** function names **)
    mul : string; add : string; sub : string;
    square : string; scmula24 : string; inv : string;

    (* TODO: add literal + copy to fiat-crypto *)
    (* bignum_literal p X :=
         store p (expr.literal (word.unsigned X[0]));
         store (p+4) (expr.literal (word.unsigned X[1]));
         ...

       bignum_copy pX pY :=
         store pX (load pY);
         store (pX+4) (load (pY+4));
         ... *)
    bignum_copy : string;
    bignum_literal : Z -> string;
  }.

(* In practice, these would be instantiated with:
   bignum := list word
   eval := fun ws => Positional.eval weight n (map word.unsigned ws)
   Bignum := (fun addr xs =>
               (emp (length xs = n) * array scalar addr xs)%sep)
   bounds := list (option zrange)
   bounded_by := (fun bs ws =>
                   list_Z_bounded_by bs (map word.unsigned ws)) *)
Class BignumRepresentation :=
  { bignum : Type;
    eval : bignum -> Z;
    Bignum :
      forall {semantics : Semantics.parameters},
        word -> bignum -> Semantics.mem -> Prop;
    bounds : Type;
    bounded_by : bounds -> bignum -> Prop;

    (* TODO: does this cover all field operation schemes, more than just
     UnsaturatedSolinas? *)
    loose_bounds : bounds;
    tight_bounds : bounds;
  }.

Section Specs.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {field_parameters : FieldParameters}.
  Context {bignum_representaton : BignumRepresentation}.

  Local Notation unop_spec name op xbounds outbounds :=
    (forall! (x : bignum) (px pout : word) (old_out : bignum),
        (fun Rr mem =>
           bounded_by xbounds x
           /\ (exists Ra, (Bignum px x * Ra)%sep mem)
           /\ (Bignum pout old_out * Rr)%sep mem)
          ===> name @ [px; pout] ===>
          (liftexists out,
           (emp ((eval out mod M = (op (eval x)) mod M)%Z
                 /\ bounded_by outbounds out)
            * Bignum pout out)%sep))
      (only parsing).

  Local Notation binop_spec name op xbounds ybounds outbounds :=
    (forall! (x y : bignum) (px py pout : word) (old_out : bignum),
        (fun Rr mem =>
           bounded_by xbounds x
           /\ bounded_by ybounds y
           /\ (exists Ra, (Bignum px x * Bignum py y * Ra)%sep mem)
           /\ (Bignum pout old_out * Rr)%sep mem)
          ===> name @ [px; py; pout] ===>
          (liftexists out,
           (emp ((eval out mod M = (op (eval x) (eval y)) mod M)%Z
                 /\ bounded_by outbounds out)
            * Bignum pout out)%sep)) (only parsing).

  Instance spec_of_mul : spec_of mul :=
    binop_spec mul Z.mul loose_bounds loose_bounds tight_bounds.
  Instance spec_of_square : spec_of square :=
    unop_spec square (fun x => Z.mul x x) loose_bounds tight_bounds.
  Instance spec_of_add : spec_of add :=
    binop_spec add Z.add tight_bounds tight_bounds loose_bounds.
  Instance spec_of_sub : spec_of sub :=
    binop_spec sub Z.sub tight_bounds tight_bounds loose_bounds.
  Instance spec_of_scmula24 : spec_of scmula24 :=
    unop_spec scmula24 (Z.mul a24) loose_bounds tight_bounds.

  (* TODO: what are the bounds for inv? *)
  Instance spec_of_inv : spec_of inv :=
    unop_spec inv Finv tight_bounds loose_bounds.

  Instance spec_of_bignum_copy : spec_of bignum_copy :=
    forall! (x : bignum) (px pout : word) (old_out : bignum),
      (sep (Bignum px x * Bignum pout old_out)%sep)
        ===> bignum_copy @ [px; pout] ===>
        (Bignum px x * Bignum pout x)%sep.

  Instance spec_of_bignum_literal (x : bignum) literal_name
    : spec_of literal_name :=
    forall! (pout : word) (old_out : bignum),
      (sep (Bignum pout old_out))
        ===> literal_name @ [pout] ===>
        (Bignum pout x)%sep.
End Specs.
Existing Instances spec_of_mul spec_of_square spec_of_add
         spec_of_sub spec_of_scmula24 spec_of_inv spec_of_bignum_copy.

Section Compile.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {field_parameters : FieldParameters}.
  Context {bignum_representaton : BignumRepresentation}.

  (* In compilation, we need to decide where to store outputs. In particular,
     we don't want to overwrite a variable that we want to use later with the
     output of some operation. The [Placeholder] alias explicitly signifies
     which Bignums are overwritable.

     TODO: in the future, it would be nice to be able to look through the
     Gallina code and see which Bignums get used later and which don't. *)
  Definition Placeholder := Bignum.

  Lemma compile_mul :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr R Rin Rout functions T (pred: T -> _ -> Prop)
      (x y out : bignum) x_ptr x_var y_ptr y_var out_ptr out_var
      k k_impl,
      spec_of_mul functions ->
      bounded_by loose_bounds x ->
      bounded_by loose_bounds y ->
      (Bignum x_ptr x * Bignum y_ptr y * Rin)%sep mem ->
      (Placeholder out_ptr out * Rout)%sep mem ->
      map.get locals x_var = Some x_ptr ->
      map.get locals y_var = Some y_ptr ->
      map.get locals out_var = Some out_ptr ->
      let v := (eval x * eval y) mod M in
      (let head := v in
       forall out m,
         eval out mod M = head ->
         bounded_by tight_bounds out ->
         sep (Bignum out_ptr out) Rout m ->
         (find k_impl
          implementing (pred (k (eval out mod M)))
          with-locals locals and-memory m and-trace tr and-rest R
          and-functions functions)) ->
      (let head := v in
       find (cmd.seq
               (cmd.call [] mul [expr.var x_var; expr.var y_var;
                                   expr.var out_var])
               k_impl)
       implementing (pred (dlet head k))
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    cbv [Placeholder] in *.
    repeat straightline'.
    handle_call; [ solve [eauto] .. | ].
    sepsimpl.
    repeat match goal with x := _ mod M |- _ =>
                                subst x end.
    match goal with H : _ mod M = ?x mod M
                    |- context [dlet (?x mod M)] =>
                    rewrite <-H
    end.
    eauto.
  Qed.

  Lemma compile_add :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr R Rin Rout functions T (pred: T -> _ -> Prop)
      (x y out : bignum) x_ptr x_var y_ptr y_var out_ptr out_var
      k k_impl,
      spec_of_add functions ->
      bounded_by tight_bounds x ->
      bounded_by tight_bounds y ->
      (Bignum x_ptr x * Bignum y_ptr y * Rin)%sep mem ->
      (Placeholder out_ptr out * Rout)%sep mem ->
      map.get locals x_var = Some x_ptr ->
      map.get locals y_var = Some y_ptr ->
      map.get locals out_var = Some out_ptr ->
      let v := (eval x + eval y) mod M in
      (let head := v in
       forall out m,
         eval out mod M = head ->
         bounded_by loose_bounds out ->
         sep (Bignum out_ptr out) Rout m ->
         (find k_impl
          implementing (pred (k (eval out mod M)))
          with-locals locals and-memory m and-trace tr and-rest R
          and-functions functions)) ->
      (let head := v in
       find (cmd.seq
               (cmd.call [] add [expr.var x_var; expr.var y_var;
                                   expr.var out_var])
               k_impl)
       implementing (pred (dlet head k))
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    cbv [Placeholder] in *.
    repeat straightline'.
    handle_call; [ solve [eauto] .. | ].
    sepsimpl.
    repeat match goal with x := _ mod M |- _ =>
                                subst x end.
    match goal with H : _ mod M = ?x mod M
                    |- context [dlet (?x mod M)] =>
                    rewrite <-H
    end.
    eauto.
  Qed.

  Lemma compile_sub :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr R Rin Rout functions T (pred: T -> _ -> Prop)
      (x y out : bignum) x_ptr x_var y_ptr y_var out_ptr out_var
      k k_impl,
      spec_of_sub functions ->
      bounded_by tight_bounds x ->
      bounded_by tight_bounds y ->
      (Bignum x_ptr x * Bignum y_ptr y * Rin)%sep mem ->
      (Placeholder out_ptr out * Rout)%sep mem ->
      map.get locals x_var = Some x_ptr ->
      map.get locals y_var = Some y_ptr ->
      map.get locals out_var = Some out_ptr ->
      let v := (eval x - eval y) mod M in
      (let head := v in
       forall out m,
         eval out mod M = head ->
         bounded_by loose_bounds out ->
         sep (Bignum out_ptr out) Rout m ->
         (find k_impl
          implementing (pred (k (eval out mod M)))
          with-locals locals and-memory m and-trace tr and-rest R
          and-functions functions)) ->
      (let head := v in
       find (cmd.seq
               (cmd.call [] sub [expr.var x_var; expr.var y_var;
                                   expr.var out_var])
               k_impl)
       implementing (pred (dlet head k))
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    cbv [Placeholder] in *.
    repeat straightline'.
    handle_call; [ solve [eauto] .. | ].
    sepsimpl.
    repeat match goal with x := _ mod M |- _ =>
                                subst x end.
    match goal with H : _ mod M = ?x mod M
                    |- context [dlet (?x mod M)] =>
                    rewrite <-H
    end.
    eauto.
  Qed.

  Lemma compile_square :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr R Rin Rout functions T (pred: T -> _ -> Prop)
      (x out : bignum) x_ptr x_var out_ptr out_var k k_impl,
      spec_of_square functions ->
      bounded_by loose_bounds x ->
      (Bignum x_ptr x * Rin)%sep mem ->
      (Placeholder out_ptr out * Rout)%sep mem ->
      map.get locals x_var = Some x_ptr ->
      map.get locals out_var = Some out_ptr ->
      let v := (eval x ^ 2) mod M in
      (let head := v in
       forall out m,
         eval out mod M = head ->
         bounded_by tight_bounds out ->
         sep (Bignum out_ptr out) Rout m ->
         (find k_impl
          implementing (pred (k (eval out mod M)))
          with-locals locals and-memory m and-trace tr and-rest R
          and-functions functions)) ->
      (let head := v in
       find (cmd.seq
               (cmd.call [] square [expr.var x_var; expr.var out_var])
               k_impl)
       implementing (pred (dlet head k))
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    cbv [Placeholder] in *.
    repeat straightline'.
    handle_call; [ solve [eauto] .. | ].
    sepsimpl.
    repeat match goal with x := _ mod M |- _ =>
                                subst x end.
    rewrite Z.pow_2_r in *.
    match goal with H : _ mod M = ?x mod M
                    |- context [dlet (?x mod M)] =>
                    rewrite <-H
    end.
    eauto.
  Qed.

  Lemma compile_scmula24 :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr R Rin Rout functions T (pred: T -> _ -> Prop)
      (x out : bignum) x_ptr x_var out_ptr out_var k k_impl,
      spec_of_scmula24 functions ->
      bounded_by loose_bounds x ->
      (Bignum x_ptr x * Rin)%sep mem ->
      (Placeholder out_ptr out * Rout)%sep mem ->
      map.get locals x_var = Some x_ptr ->
      map.get locals out_var = Some out_ptr ->
      let v := (a24 * eval x) mod M in
      (let head := v in
       forall out m,
         eval out mod M = head ->
         bounded_by tight_bounds out ->
         sep (Bignum out_ptr out) Rout m ->
         (find k_impl
          implementing (pred (k (eval out mod M)))
          with-locals locals and-memory m and-trace tr and-rest R
          and-functions functions)) ->
      (let head := v in
       find (cmd.seq
               (cmd.call [] scmula24 [expr.var x_var; expr.var out_var])
               k_impl)
       implementing (pred (dlet head k))
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    cbv [Placeholder] in *.
    repeat straightline'.
    handle_call; [ solve [eauto] .. | ].
    sepsimpl.
    repeat match goal with x := _ mod M |- _ =>
                                subst x end.
    match goal with H : _ mod M = ?x mod M
                    |- context [dlet (?x mod M)] =>
                    rewrite <-H
    end.
    eauto.
  Qed.

  Lemma compile_bignum_copy :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr R R' functions T (pred: T -> _ -> Prop)
      (x out : bignum) x_ptr x_var out_ptr out_var k k_impl,
      spec_of_bignum_copy functions ->
      (Bignum x_ptr x * Placeholder out_ptr out * R')%sep mem ->
      map.get locals x_var = Some x_ptr ->
      map.get locals out_var = Some out_ptr ->
      let v := eval x in
      (let head := v in
       forall m,
         (Bignum x_ptr x * Bignum out_ptr x * R')%sep m ->
         (find k_impl
          implementing (pred (k head))
          with-locals locals and-memory m and-trace tr and-rest R
          and-functions functions)) ->
      (let head := v in
       find (cmd.seq
               (cmd.call [] bignum_copy [expr.var x_var; expr.var out_var])
               k_impl)
       implementing (pred (dlet head k))
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    cbv [Placeholder] in *.
    repeat straightline'.
    handle_call; [ solve [eauto] .. | ].
    sepsimpl. auto.
  Qed.

  Lemma compile_bignum_literal :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr R R' functions T (pred: T -> _ -> Prop)
      (x out : bignum) out_ptr out_var k k_impl,
      let literal_name := bignum_literal (eval x) in
      spec_of_bignum_literal x literal_name functions ->
      (Placeholder out_ptr out * R')%sep mem ->
      map.get locals out_var = Some out_ptr ->
      let v := eval x in
      (let head := v in
       forall m,
         (Bignum out_ptr x * R')%sep m ->
         (find k_impl
          implementing (pred (k head))
          with-locals locals and-memory m and-trace tr and-rest R
          and-functions functions)) ->
      (let head := v in
       find (cmd.seq
               (cmd.call [] literal_name [expr.var out_var])
               k_impl)
       implementing (pred (dlet head k))
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    cbv [Placeholder] in *.
    repeat straightline'.
    (* inline straightline_call because typeclass instance for spec has
       arguments and inference won't find it *)
    lazymatch goal with
      Hcall : spec_of_bignum_literal _ _ _ |- _ =>
      eapply Proper_call; cycle -1;
        [ eapply Hcall | .. ];
        [ .. | intros ? ? ? ? ]
    end; try ecancel_assumption.
    cbv[postcondition_for] in *; repeat straightline;
      destruct_lists_of_known_length; repeat straightline.
    sepsimpl. auto.
  Qed.

  (* noop indicating that the last argument should store output *)
  Definition overwrite1 {A B} := @id (A -> B).
  (* noop indicating that the 2nd-to-last argument should store output *)
  Definition overwrite2 {A B C} := @id (A -> B -> C).

  Lemma compile_compose_l :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr R Rout functions T (pred: T -> _ -> Prop)
      (op1 op2 : Z -> Z -> Z)
      x y z out out_ptr out_var k k_impl,
      (Placeholder out_ptr out * Rout)%sep mem ->
      map.get locals out_var = Some out_ptr ->
      let v := ((op2 (op1 x y mod M) z)) mod M in
      (let head := v in
       (find k_impl
        implementing (pred (dlet (op1 x y mod M)
        (fun xy => dlet ((overwrite2 op2) xy z mod M) k)))
        with-locals locals and-memory mem and-trace tr and-rest R
        and-functions functions)) ->
      (let head := v in
       find k_impl
       implementing (pred (dlet head k))
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    cbv [Placeholder overwrite1 overwrite2] in *.
    repeat straightline'. auto.
  Qed.

  Lemma compile_compose_r :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr R Rout functions T (pred: T -> _ -> Prop)
      (op1 op2 : Z -> Z -> Z)
      x y z out out_ptr out_var k k_impl,
      (Placeholder out_ptr out * Rout)%sep mem ->
      map.get locals out_var = Some out_ptr ->
      let v := ((op2 z (op1 x y mod M))) mod M in
      (let head := v in
       (find k_impl
        implementing (pred (dlet (op1 x y mod M)
        (fun xy => dlet ((overwrite1 op2) z xy mod M) k)))
        with-locals locals and-memory mem and-trace tr and-rest R
        and-functions functions)) ->
      (let head := v in
       find k_impl
       implementing (pred (dlet head k))
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    cbv [Placeholder overwrite1 overwrite2] in *.
    repeat straightline'. auto.
  Qed.

  Lemma compile_overwrite1 :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr R Rin functions T (pred: T -> _ -> Prop)
      (x : Z) (op : Z -> Z -> Z) (y : bignum) y_ptr y_var k k_impl,
      (Bignum y_ptr y * Rin)%sep mem ->
      map.get locals y_var = Some y_ptr ->
      let v := ((overwrite1 op) x (eval y mod M)) mod M in
      let v' := (op x (eval y mod M)) mod M in
      (let __ := 0 in (* placeholder *)
       forall m,
         sep (Placeholder y_ptr y) Rin m ->
         (find k_impl
          implementing (pred (dlet v' k))
          with-locals locals and-memory m and-trace tr and-rest R
          and-functions functions)) ->
      (let head := v in
       find k_impl
       implementing (pred (dlet head k))
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    cbv [Placeholder] in *.
    repeat straightline'. auto.
  Qed.

  Lemma compile_overwrite2 :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr R Rin functions T (pred: T -> _ -> Prop)
      (y : Z) (op : Z -> Z -> Z) (x : bignum) x_ptr x_var k k_impl,
      (Bignum x_ptr x * Rin)%sep mem ->
      map.get locals x_var = Some x_ptr ->
      let v := ((overwrite2 op) (eval x mod M) y) mod M in
      let v' := (op (eval x mod M) y) mod M in
      (let __ := 0 in (* placeholder *)
       forall m,
         sep (Placeholder x_ptr x) Rin m ->
         (find k_impl
          implementing (pred (dlet v' k))
          with-locals locals and-memory m and-trace tr and-rest R
          and-functions functions)) ->
      (let head := v in
       find k_impl
       implementing (pred (dlet head k))
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    cbv [Placeholder] in *.
    repeat straightline'. auto.
  Qed.
End Compile.

Module Z.
  (* helper for Zpow_mod *)
  Lemma pow_mod_nonneg a b m :
    0 <= b -> (a ^ b) mod m = ((a mod m) ^ b) mod m.
  Proof.
    intros. revert a m.
    apply natlike_ind with (x:=b); intros;
      repeat first [ rewrite Z.pow_0_r
                   | rewrite Z.pow_succ_r by auto
                   | reflexivity
                   | solve [auto] ]; [ ].
    Z.push_mod.
    match goal with
      H : context [ (_ ^ _) mod _ = (_ ^ _) mod _ ] |- _ =>
      rewrite H end.
    Z.push_pull_mod. reflexivity.
  Qed.

  (* TODO: upstream to coqutil's Z.pull_mod *)
  Lemma pow_mod a b m : (a ^ b) mod m = ((a mod m) ^ b) mod m.
  Proof.
    destruct (Z_le_dec 0 b); auto using pow_mod_nonneg; [ ].
    rewrite !Z.pow_neg_r by lia. reflexivity.
  Qed.
End Z.

(* TODO: replace with Z.pull_mod once Zpow_mod is upstreamed *)
Ltac pull_mod :=
  repeat first [ progress Z.pull_mod
               | rewrite <-Z.pow_mod ].

Ltac field_compile_step :=
  Z.push_pull_mod; pull_mod;
  first [ simple eapply compile_mul
        | simple eapply compile_add
        | simple eapply compile_sub
        | simple eapply compile_square
        | simple eapply compile_scmula24 ].

Ltac compile_compose_step :=
  Z.push_mod;
  first [ simple eapply compile_compose_l
        | simple eapply compile_compose_r
        | simple eapply compile_overwrite1
        | simple eapply compile_overwrite2 ];
  [ solve [repeat compile_step] .. | intros ].

Ltac free p := change (Bignum p) with (Placeholder p) in *.
