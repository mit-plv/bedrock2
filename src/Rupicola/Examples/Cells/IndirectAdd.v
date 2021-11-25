(** A Rupicola version of the indirect_add example in Bedrock2. **)
Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.Cells.Cells.

Section with_parameters.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {wordok : word.ok word} {mapok : map.ok mem}.
  Context {localsok : map.ok locals}.
  Context {envok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Local Notation cell := (@cell width BW word).

  Definition indirect_add (b c: cell) :=
    let/n vb := get b in
    let/n vc := get c in
    let/n r := word.add vb vc in
    let/n a := put r in
    a.

  Instance spec_of_indirect_add : spec_of "indirect_add" :=
    fnspec! "indirect_add" pa pb pc / a Ra b Rb c Rc,
    { requires t m :=
        (cell_value pa a ⋆ Ra &&&
         cell_value pb b ⋆ Rb &&&
         cell_value pc c ⋆ Rc) m;
      ensures t' m' :=
        t = t' /\
        (cell_value pa (indirect_add b c) ⋆ Ra) m' }.

  Derive indirect_add_br2fn SuchThat
         (defn! "indirect_add"("a", "b", "c") { indirect_add_br2fn },
          implements indirect_add)
         As indirect_add_br2fn_ok.
  Proof.
    compile.
  Qed.

  (* FIXME auto-generate lemma from pre-post condition pair? *)

  Lemma compile_indirect_add : forall {tr mem locals functions} a b c,
    let v := indirect_add b c in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
      a_var b_expr c_expr pa pb pc Ra Rb Rc,

      map.get locals a_var = Some pa ->
      (cell_value pa a ⋆ Ra) mem ->

      (cell_value pb b ⋆ Rb) mem ->
      WeakestPrecondition.dexpr mem locals b_expr pb ->

      (cell_value pc c ⋆ Rc) mem ->
      WeakestPrecondition.dexpr mem locals c_expr pc ->

      (_: spec_of "indirect_add") functions ->

      (let v := v in
       forall m,
         sep (cell_value pa v) Ra m ->
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
      cmd.seq (cmd.call [] "indirect_add" [expr.var a_var; b_expr; c_expr])
              k_impl
      <{ pred (nlet_eq [a_var] v k) }>.
  Proof.
    unfold unsep.
    repeat straightline.
    repeat (eexists; split; eauto).
    simpl; repeat (eapply WeakestPrecondition_dexpr_expr; eauto).
    straightline_call; unfold unsep in *; eauto; [].
    intuition subst.
    repeat (eexists; split; eauto).
  Qed.

  Hint Extern 1 => simple eapply compile_indirect_add; shelve : compiler.

  Definition indirect_add_twice (a b: cell) :=
    let/n a := indirect_add a b in
    let/n a := indirect_add a b in
    a.

  Instance spec_of_indirect_add_twice : spec_of "indirect_add_twice" :=
    fnspec! "indirect_add_twice" pa pb / a b R,
    { requires t m :=
        (cell_value pa a ⋆ cell_value pb b ⋆ R) m;
      ensures t' m' :=
        t = t' /\ (cell_value pa (indirect_add_twice a b) ⋆ cell_value pb b ⋆ R) m' }.

  Derive indirect_add_twice_br2fn SuchThat
         (defn! "indirect_add_twice"("a", "b") { indirect_add_twice_br2fn },
          implements indirect_add_twice using ["indirect_add"])
         As indirect_add_twice_br2fn_ok.
  Proof.
    compile.
  Qed.

  Definition indirect_add_three (a b c: cell) :=
    let/n a := indirect_add a b in
    let/n a := indirect_add a c in
    a.

  (* Quick sanity check that Rupicola's notations unfold into code that's
     decently nice to work with: *)
  Notation "⟨ v ⟩" := {| data := v |}.
  Goal forall a b c, indirect_add_three ⟨a⟩ ⟨b⟩ ⟨c⟩ = ⟨word.add (word.add a b) c⟩.
    reflexivity.
  Qed.

  Instance spec_of_indirect_add_three : spec_of "indirect_add_three" :=
    fnspec! "indirect_add_three" pa pb pc / a b c Rb R,
    { requires t m :=
        (cell_value pa a ⋆ cell_value pc c ⋆ R &&&
         cell_value pb b ⋆ Rb) m;
      ensures t' m' :=
        t = t' /\
        (cell_value pa (indirect_add_three a b c) ⋆ cell_value pc c ⋆ R) m' }.

  Derive indirect_add_three_br2fn SuchThat
         (defn! "indirect_add_three"("a", "b", "c") { indirect_add_three_br2fn },
          implements indirect_add_three using ["indirect_add"])
         As indirect_add_three_br2fn_ok.
  Proof.
    compile.
  Qed.

  Definition indirect_add_three' (a b c: cell) :=
    let/n v := stack (indirect_add a b) in
    let/n out := indirect_add v c in
    out.

  Instance spec_of_indirect_add_three' : spec_of "indirect_add_three'" :=
    fnspec! "indirect_add_three'" pout pa pb pc / out a b c Ra Rb Rc R,
    { requires t m :=
        (cell_value pout out ⋆ R &&&
         cell_value pa a ⋆ Ra &&&
         cell_value pb b ⋆ Rb &&&
         cell_value pc c ⋆ Rc) m;
      ensures t' m' :=
        t = t' /\
        (cell_value pout (indirect_add_three' a b c) ⋆ R) m' }.

  Derive indirect_add_three'_br2fn SuchThat
         (defn! "indirect_add_three'"("out", "a", "b", "c") { indirect_add_three'_br2fn },
          implements indirect_add_three' using ["indirect_add"])
    As indirect_add_three'_br2fn_ok.
  Proof.
    compile.
  Qed.

  Arguments indirect_add_three'_br2fn /.
  Eval simpl in indirect_add_three'_br2fn.
End with_parameters.
