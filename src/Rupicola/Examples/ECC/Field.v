Require Import Rupicola.Lib.Api.
Local Open Scope Z_scope.

Class FieldParameters :=
  { (** mathematical parameters **)
    M_pos : positive; (* modulus *)
    M : Z := Z.pos M_pos;
    a24 : Z; (* (a+2) / 4 or (a-2) / 4, depending on the implementation *)
    Finv : Z -> Z; (* modular inverse in Z/M *)
    (** function names **)
    mul : string; add : string; sub : string;
    square : string; scmula24 : string; inv : string;

    (* TODO: add literal + copy to fiat-crypto *)
    (* N.B. in current form, bignum_literal only works for literals that fit in
       a word -- what would a more general form look like? Is it needed? *)
    (* bignum_literal p x :=
         store p (expr.literal x);
         store (p+4) (expr.literal 0);
         ...

       bignum_copy pX pY :=
         store pX (load pY);
         store (pX+4) (load (pY+4));
         ... *)
    bignum_copy : string;
    bignum_literal : string;
  }.

Lemma M_nonzero {fp : FieldParameters} : M <> 0.
Proof. cbv [M]. congruence. Qed.

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

(* TODO: copy the specs back over into fiat-crypto and prove that they are
   obeyed to validate the slight rephrasings here *)
Section Specs.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {field_parameters : FieldParameters}.
  Context {bignum_representaton : BignumRepresentation}.

  Class UnOp (name: string) :=
    { un_model: Z -> Z;
      un_xbounds: bounds;
      un_outbounds: bounds }.

  Definition unop_spec {name} (op: UnOp name) :=
    fnspec! name (px pout : word) / (x : bignum) (old_out : bignum) Rr,
    { requires fns tr mem :=
        bounded_by un_xbounds x
        /\ (exists Ra, (Bignum px x * Ra)%sep mem)
        /\ (Bignum pout old_out * Rr)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists out,
          eval out mod M = (un_model (eval x mod M)) mod M
          /\ bounded_by un_outbounds out
          /\ (Bignum pout out * Rr)%sep mem' }.

  Definition Znum (ptr : word) (z : Z) (mem : Semantics.mem) :=
      (exists b : bignum, (z = eval b mod M) /\
                             Bignum ptr b mem).

   Definition unop_Z_spec {name} (op: UnOp name) :=
    fnspec! name (pz pout : word) / (z : Z) (old_out : Z) Rr,
    { requires fns tr mem :=
        (* bounded_by un_xbounds x *)
        (exists Ra, (Znum pz z * Ra)%sep mem)
        /\ (Znum pout old_out * Rr)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
          (Znum pout ((un_model z) mod M) * Rr)%sep mem' }.

  Instance spec_of_UnOp {name} (op: UnOp name) : spec_of name :=
    unop_spec op.

  Instance spec_of_Z_UnOp {name} (op: UnOp name) : spec_of name :=
    unop_Z_spec op.

  Class BinOp (name: string) :=
    { bin_model: Z -> Z -> Z;
      bin_xbounds: bounds;
      bin_ybounds: bounds;
      bin_outbounds: bounds }.

  Definition binop_spec  {name} (op: BinOp name) :=
    fnspec! name (px py pout : word) / (x y: bignum) (old_out : bignum) Rr,
    { requires fns tr mem :=
        bounded_by bin_xbounds x
        /\ bounded_by bin_ybounds y
        /\ (exists Ra, (Bignum px x * Bignum py y * Ra)%sep mem)
        /\ (Bignum pout old_out * Rr)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists out,
          eval out mod M = (bin_model (eval x mod M) (eval y mod M)) mod M
          /\ bounded_by bin_outbounds out
          /\ (Bignum pout out * Rr)%sep mem' }.

   Definition binop_Z_spec  {name} (op: BinOp name) :=
    fnspec! name (px py pout : word) / (x y: Z) (old_out : Z) Rr,
    { requires fns tr mem :=
       (* bounded_by bin_xbounds x
        /\ bounded_by bin_ybounds y *)
        (exists Ra, (Znum px x * Znum py y * Ra)%sep mem)
        /\ (Znum pout old_out * Rr)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        (Znum pout ((bin_model x y) mod M) * Rr)%sep mem' }.

  Instance spec_of_BinOp {name} (op: BinOp name) : spec_of name :=
    binop_spec op.

  Instance spec_of_Z_BinOp {name} (op: BinOp name) : spec_of name :=
    binop_Z_spec op.

  Instance bin_mul : BinOp mul :=
    {| bin_model := Z.mul; bin_xbounds := loose_bounds; bin_ybounds := loose_bounds; bin_outbounds := tight_bounds |}.
  Instance un_square : UnOp square :=
    {| un_model := fun x => Z.pow x 2; un_xbounds := loose_bounds; un_outbounds := tight_bounds |}.
  Instance bin_add : BinOp add :=
    {| bin_model := Z.add; bin_xbounds := tight_bounds; bin_ybounds := tight_bounds; bin_outbounds := loose_bounds |}.
  Instance bin_sub : BinOp sub :=
    {| bin_model := Z.sub; bin_xbounds := tight_bounds; bin_ybounds := tight_bounds; bin_outbounds := loose_bounds |}.
  Instance un_scmula24 : UnOp scmula24 :=
    {| un_model := Z.mul a24; un_xbounds := loose_bounds; un_outbounds := tight_bounds |}.
  Instance un_inv : UnOp inv := (* TODO: what are the bounds for inv? *)
    {| un_model := fun x => Finv (x mod M); un_xbounds := tight_bounds; un_outbounds := loose_bounds |}.

  Instance spec_of_bignum_copy : spec_of bignum_copy :=
    fnspec! bignum_copy (px pout : word) / (x : bignum) (old_out : bignum) R,
    { requires fns tr mem :=
        (Bignum px x * Bignum pout old_out * R)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        (Bignum px x * Bignum pout x * R)%sep mem' }.

  Instance spec_of_bignum_literal : spec_of bignum_literal :=
    fnspec! bignum_literal (x pout : word) / (old_out : bignum) R,
    { requires fns tr mem :=
        (Bignum pout old_out * R)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists X, eval X mod M = word.unsigned x mod M
             /\ bounded_by tight_bounds X
             /\ (Bignum pout X * R)%sep mem' }.
End Specs.

Existing Instances spec_of_BinOp bin_mul un_square bin_add bin_sub
         un_scmula24 un_inv spec_of_bignum_copy spec_of_bignum_literal.

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
     Gallina code and see which Bignums get used later and which don't.

     FIXME: we now have explicit names in bindings, which should allow us to get
     rid of [Placeholder] annotations. *)
  Definition Placeholder := Bignum.

  Lemma compile_binop {name} {op: BinOp name}
        {tr mem locals functions} x y:
    let v := (bin_model (eval x mod M) (eval y mod M)) mod M in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
      Rin Rout (out : bignum) x_ptr x_var y_ptr y_var out_ptr out_var,

      (_: spec_of name) functions ->
      bounded_by bin_xbounds x ->
      bounded_by bin_ybounds y ->

      map.get locals out_var = Some out_ptr ->
      (Placeholder out_ptr out * Rout)%sep mem ->

      (Bignum x_ptr x * Bignum y_ptr y * Rin)%sep mem ->
      map.get locals x_var = Some x_ptr ->
      map.get locals y_var = Some y_ptr ->

      (let v := v in
       forall out m (Heq: eval out mod M = v),
         bounded_by bin_outbounds out ->
         sep (Bignum out_ptr out) Rout m ->
         (<{ Trace := tr;
             Memory := m;
             Locals := locals;
             Functions := functions }>
          k_impl
          <{ pred (k v eq_refl) }>)) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (cmd.call [] name [expr.var x_var; expr.var y_var;
                          expr.var out_var])
        k_impl
      <{ pred (nlet_eq [out_var] v k) }>.
  Proof.
    cbv [Placeholder] in *.
    repeat straightline'.
    handle_call; [ solve [eauto] .. | ].
    repeat straightline'.
    eauto.
  Qed.

  Lemma compile_Z_binop {name} {op: BinOp name}
        {tr mem locals functions} x y:
    let v := (bin_model x y) mod M in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
      Rin Rout (out : Z) x_ptr x_var y_ptr y_var out_ptr out_var,

      let spec := (spec_of_Z_BinOp _: spec_of name) in spec functions ->
      (* bounded_by bin_xbounds x ->
      bounded_by bin_ybounds y -> *)

      map.get locals out_var = Some out_ptr ->
      (Znum out_ptr out * Rout)%sep mem ->

      (Znum x_ptr x * Znum y_ptr y * Rin)%sep mem ->
      map.get locals x_var = Some x_ptr ->
      map.get locals y_var = Some y_ptr ->

     (let v := v in
       forall m,
         (* bounded_by bin_outbounds out -> *)
         sep (Znum out_ptr v) Rout m ->
         (<{ Trace := tr;
             Memory := m;
             Locals := locals;
             Functions := functions }>
          k_impl
          <{ pred (k v eq_refl) }>)) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (cmd.call [] name [expr.var x_var; expr.var y_var;
                          expr.var out_var])
        k_impl
      <{ pred (nlet_eq [out_var] v k) }>.
  Proof.
    repeat straightline'.
    handle_call; [ solve [eauto] .. | ].
    repeat straightline'.
    eauto.
  Qed.

  Lemma compile_unop {name} (op: UnOp name) {tr mem locals functions} x:
    let v := un_model (eval x mod M) mod M in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
      Rin Rout (out : bignum) x_ptr x_var out_ptr out_var,

      let spec := (spec_of_UnOp _: spec_of name) in spec functions ->
      bounded_by un_xbounds x ->

      map.get locals out_var = Some out_ptr ->
      (Placeholder out_ptr out * Rout)%sep mem ->

      (Bignum x_ptr x * Rin)%sep mem ->
      map.get locals x_var = Some x_ptr ->

      (let v := v in
       forall out m (Heq: eval out mod M = v),
         bounded_by un_outbounds out ->
         sep (Bignum out_ptr out) Rout m ->
         (<{ Trace := tr;
             Memory := m;
             Locals := locals;
             Functions := functions }>
          k_impl
          (* <{ (rew [fun v => P v -> predicate)] Heq in pred) (k (eval out mod M) Heq) }>)) -> *)
          <{ pred (k v eq_refl) }>)) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (cmd.call [] name [expr.var x_var; expr.var out_var])
        k_impl
      <{ pred (nlet_eq [out_var] v k) }>.
  Proof.
    intros.
    cbv [Placeholder] in *.
    repeat straightline'.
    Print Ltac straightline_call.
    handle_call; [ solve [eauto] .. | sepsimpl ].
    repeat straightline'.
    eauto.
  Qed.

  Lemma compile_Z_unop {name} (op: UnOp name) {tr mem locals functions} x:
    let v := un_model x mod M in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
      Rin Rout (out : Z) x_ptr x_var out_ptr out_var,

      let spec := (spec_of_Z_UnOp _: spec_of name) in spec functions ->
      (* bounded_by un_xbounds x -> *)

      map.get locals out_var = Some out_ptr ->
      (Znum out_ptr out * Rout)%sep mem ->

      (Znum x_ptr x * Rin)%sep mem ->
      map.get locals x_var = Some x_ptr ->

      (let v := v in
       forall m,
         (* bounded_by un_outbounds out -> *)
         sep (Znum out_ptr v) Rout m ->
         (<{ Trace := tr;
             Memory := m;
             Locals := locals;
             Functions := functions }>
          k_impl
          (* <{ (rew [fun v => P v -> predicate)] Heq in pred) (k (eval out mod M) Heq) }>)) -> *)
          <{ pred (k v eq_refl) }>)) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (cmd.call [] name [expr.var x_var; expr.var out_var])
        k_impl
      <{ pred (nlet_eq [out_var] v k) }>.
  Proof.
    repeat straightline'.
    handle_call; [ solve [eauto] .. | sepsimpl ].
    repeat straightline'.
    eauto.
  Qed.

  Ltac cleanup_op_lemma lem := (* This makes [simple apply] work *)
    let lm := fresh in
    let op := match lem with _ _ ?op => op end in
    let op_hd := term_head op in
    let simp proj :=
        (let hd := term_head proj in
         let reduced := (eval cbv [op_hd hd] in proj) in
         change proj with reduced in (type of lm)) in
    pose lem as lm;
    first [ simp (bin_model (BinOp := op));
            simp (bin_xbounds (BinOp := op));
            simp (bin_ybounds (BinOp := op));
            simp (bin_outbounds (BinOp := op))
          | simp (un_model (UnOp := op));
            simp (un_xbounds (UnOp := op));
            simp (un_outbounds (UnOp := op)) ];
    let t := type of lm in
    let t := (eval cbv beta in t) in
    exact (lm: t).

  Notation make_bin_lemma op :=
    ltac:(cleanup_op_lemma (@compile_binop _ op)) (only parsing).

  Notation make_Z_bin_lemma op :=
    ltac:(cleanup_op_lemma (@compile_Z_binop _ op)) (only parsing).

  Definition compile_mul := make_bin_lemma bin_mul.
  Definition compile_add := make_bin_lemma bin_add.
  Definition compile_sub := make_bin_lemma bin_sub.

  Definition compile_Z_mul := make_Z_bin_lemma bin_mul.
  Definition compile_Z_add := make_Z_bin_lemma bin_add.
  Definition compile_Z_sub := make_Z_bin_lemma bin_sub.

  Notation make_un_lemma op :=
    ltac:(cleanup_op_lemma (@compile_unop _ op)) (only parsing).

  Notation make_Z_un_lemma op :=
    ltac:(cleanup_op_lemma (@compile_Z_unop _ op)) (only parsing).

  Definition compile_square := make_un_lemma un_square.
  Definition compile_scmula24 := make_un_lemma un_scmula24.
  Definition compile_inv := make_un_lemma un_inv.

  Definition compile_Z_square := make_Z_un_lemma un_square.
  Definition compile_Z_scmula24 := make_Z_un_lemma un_scmula24.
  Definition compile_Z_inv := make_Z_un_lemma un_inv.


  Lemma compile_bignum_copy {tr mem locals functions} x :
    let v := (eval x mod M)%Z in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
      R (out : bignum) x_ptr x_var out_ptr out_var,

      spec_of_bignum_copy functions ->

      map.get locals out_var = Some out_ptr ->

      (Bignum x_ptr x * Placeholder out_ptr out * R)%sep mem ->
      map.get locals x_var = Some x_ptr ->

      (let v := v in
       forall m,
         (Bignum x_ptr x * Bignum out_ptr x * R)%sep m ->
         (<{ Trace := tr;
             Memory := m;
             Locals := locals;
             Functions := functions }>
          k_impl
          <{ pred (k v eq_refl) }>)) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (cmd.call [] bignum_copy [expr.var x_var; expr.var out_var])
        k_impl
      <{ pred (nlet_eq [out_var] v k) }>.
  Proof.
    cbv [Placeholder] in *.
    repeat straightline'.
    handle_call; [ solve [eauto] .. | sepsimpl ].
    repeat straightline'.
    use_hyp_with_matching_cmd; eauto;
      ecancel_assumption.
  Qed.

  Lemma compile_bignum_literal {tr mem locals functions} x:
    let v := (x mod M)%Z in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
      R (wx : word) (out : bignum) out_ptr out_var,

      spec_of_bignum_literal functions ->

      map.get locals out_var = Some out_ptr ->
      (Placeholder out_ptr out * R)%sep mem ->

      word.unsigned wx = x ->

      (let v := v in
       forall X m,
         (Bignum out_ptr X * R)%sep m ->
         eval X mod M = v ->
         bounded_by tight_bounds X ->
         (<{ Trace := tr;
             Memory := m;
             Locals := locals;
             Functions := functions }>
          k_impl
          <{ pred (k v eq_refl) }>)) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (cmd.call [] bignum_literal
                  [expr.literal x; expr.var out_var])
        k_impl
      <{ pred (nlet_eq [out_var] v k) }>.
  Proof.
    cbv [Placeholder] in *.
    repeat straightline'. subst.
    handle_call; [ solve [eauto] .. | ].
    repeat straightline'.
    rewrite @word.of_Z_unsigned in * by typeclasses eauto.
    eauto.
  Qed.

  (* noop indicating that the last argument should store output *)
  Definition overwrite1 {A B} := @id (A -> B).
  (* noop indicating that the 2nd-to-last argument should store output *)
  Definition overwrite2 {A B C} := @id (A -> B -> C).

  (* FIXME remove overwrites; use variable names instead *)

  Lemma compile_compose_l {tr mem locals functions} (op1 op2 : Z -> Z -> Z) x y z:
    let v := ((op2 (op1 x y mod M) z)) mod M in
    forall {T} {pred: T -> predicate} {k: Z -> T} {k_impl}
      Rout out out_ptr out_var,
      map.get locals out_var = Some out_ptr ->
      (Placeholder out_ptr out * Rout)%sep mem ->
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       k_impl
       <{ pred (dlet (op1 x y mod M)
                     (fun xy => dlet ((overwrite2 op2) xy z mod M) k)) }>) ->
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       k_impl
       <{ pred (dlet v k) }>).
  Proof.
    cbv [Placeholder overwrite1 overwrite2] in *.
    repeat straightline'. auto.
  Qed.

  Lemma compile_compose_r {tr mem locals functions} (op1 op2 : Z -> Z -> Z) x y z:
    let v := ((op2 z (op1 x y mod M))) mod M in
    forall {T} {pred: T -> predicate} {k: Z -> T} {k_impl}
      Rout out out_ptr out_var,
      map.get locals out_var = Some out_ptr ->
      (Placeholder out_ptr out * Rout)%sep mem ->
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       k_impl
       <{ pred (dlet (op1 x y mod M)
                     (fun xy => dlet ((overwrite1 op2) z xy mod M) k)) }>) ->
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       k_impl
       <{ pred (dlet v k) }>).
  Proof.
    cbv [Placeholder overwrite1 overwrite2] in *.
    repeat straightline'. auto.
  Qed.

  Lemma compile_overwrite1 {tr mem locals functions} (x : Z) (op : Z -> Z -> Z) (y : bignum):
    let v := ((overwrite1 op) x (eval y mod M)) mod M in
    forall {T} {pred: T -> predicate} {k: Z -> T} {k_impl}
      Rin y_ptr y_var,
      (Bignum y_ptr y * Rin)%sep mem ->
      map.get locals y_var = Some y_ptr ->
      let v' := (op x (eval y mod M)) mod M in
      (let __ := 0 in (* placeholder *)
       forall m,
         sep (Placeholder y_ptr y) Rin m ->
         <{ Trace := tr;
            Memory := m;
            Locals := locals;
            Functions := functions }>
         k_impl
         <{ pred (dlet v' k) }>) ->
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       k_impl
       <{ pred (dlet v k) }>).
  Proof.
    cbv [Placeholder] in *.
    repeat straightline'. auto.
  Qed.

  Lemma compile_overwrite2 {tr mem locals functions} (y : Z) (op : Z -> Z -> Z) (x : bignum):
    let v := ((overwrite2 op) (eval x mod M) y) mod M in
    forall {T} {pred: T -> predicate} {k: Z -> T} {k_impl}
      Rin x_ptr x_var,
      (Bignum x_ptr x * Rin)%sep mem ->
      map.get locals x_var = Some x_ptr ->
      let v' := (op (eval x mod M) y) mod M in
      (let __ := 0 in (* placeholder *)
       forall m,
         sep (Placeholder x_ptr x) Rin m ->
         <{ Trace := tr;
            Memory := m;
            Locals := locals;
            Functions := functions }>
         k_impl
         <{ pred (dlet v' k) }>) ->
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       k_impl
       <{ pred (dlet v k) }>).
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
        | simple eapply compile_scmula24
        | simple eapply compile_inv ].

Ltac compile_compose_step :=
  Z.push_mod;
  first [ simple eapply compile_compose_l
        | simple eapply compile_compose_r
        | simple eapply compile_overwrite1
        | simple eapply compile_overwrite2 ];
  [ solve [repeat compile_step] .. | intros ].

Ltac free p := change (Bignum p) with (Placeholder p) in *.
