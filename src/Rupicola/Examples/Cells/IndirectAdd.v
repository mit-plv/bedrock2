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

  Definition indirect_add (a b c: cell) :=
    let/n vb := get b in
    let/n vc := get c in
    let/n r := word.add vb vc in
    let/n a := put r a in
    a.

  Local Notation "m =* P" := (P%sep m) (at level 70, only parsing).

  Instance spec_of_indirect_add : spec_of "indirect_add" :=
    fnspec! "indirect_add" pa pb pc / a Ra b Rb c Rc,
    { requires t m :=
        m =* cell_value pa a * Ra /\ m =* cell_value pb b * Rb /\ m =* cell_value pc c * Rc;
      ensures t' m' :=
        t = t' /\ m' =* cell_value pa (indirect_add a b c) * Ra }.

  Derive indirect_add_body SuchThat
         (defn! "indirect_add"("a", "b", "c") { indirect_add_body },
          implements indirect_add)
         As indirect_add_body_correct.
  Proof.
    compile.
  Qed.

  (* FIXME auto-generate lemma from pre-post condition pair? *)

  Lemma compile_indirect_add : forall {tr mem locals functions} a b c,
    let v := indirect_add a b c in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
      va vb vc pa pb pc Ra Rb Rc,

      (cell_value pa a ⋆ Ra) mem ->
      (cell_value pb b ⋆ Rb) mem ->
      (cell_value pc c ⋆ Rc) mem ->

      map.get locals va = Some pa ->
      map.get locals vb = Some pb ->
      map.get locals vc = Some pc ->

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
      cmd.seq (cmd.call [] "indirect_add" [expr.var va; expr.var vb; expr.var vc])
              k_impl
      <{ pred (nlet_eq [va] v k) }>.
  Proof.
    repeat straightline.
    repeat (eexists; split; eauto).
    straightline_call; eauto.
    intuition subst.
    repeat (eexists; split; eauto).
  Qed.

  Hint Extern 1 => simple eapply compile_indirect_add; shelve : compiler.

  Definition indirect_add_twice (a b: cell) :=
    let/n a := indirect_add a a b in
    let/n a := indirect_add a a b in
    a.

  Instance spec_of_indirect_add_twice : spec_of "indirect_add_twice" :=
    fnspec! "indirect_add_twice" pa pb / a b R,
    { requires t m :=
        m =* cell_value pa a * cell_value pb b * R;
      ensures t' m' :=
        t = t' /\ m' =* cell_value pa (indirect_add_twice a b) * cell_value pb b * R }.

  Derive indirect_add_twice_body SuchThat
         (defn! "indirect_add_twice"("a", "b") { indirect_add_twice_body },
          implements indirect_add_twice using ["indirect_add"])
         As indirect_add_twice_body_correct.
  Proof.
    compile.
  Qed.

  Definition indirect_add_three (a b c: cell) :=
    let/n a := indirect_add a a b in
    let/n a := indirect_add a a c in
    a.

  (* The notations unfold into something decently nice: *)
  Notation "⟨ v ⟩" := {| data := v |}.
  Goal forall a b c, indirect_add_three ⟨a⟩ ⟨b⟩ ⟨c⟩ = ⟨word.add (word.add a b) c⟩.
    reflexivity.
  Qed.

  Instance spec_of_indirect_add_three : spec_of "indirect_add_three" :=
    fnspec! "indirect_add_three" pa pb pc / a b c Rb R,
    { requires t m :=
        m =* cell_value pa a * cell_value pc c * R /\ m =* cell_value pb b * Rb;
      ensures t' m' :=
        t = t' /\ m' =* cell_value pa (indirect_add_three a b c) * cell_value pc c * R }.

  Derive indirect_add_three_body SuchThat
         (defn! "indirect_add_three"("a", "b", "c") { indirect_add_three_body },
          implements indirect_add_three using ["indirect_add"])
         As indirect_add_three_body_correct.
  Proof.
    compile.
  Qed.

  (* TODO: Import the `indirect_add_three'` example from Bedrock's indirect_add.v

  Definition indirect_add_three' : Syntax.func := let a := "a" in let b := "b" in let c := "c" in let out := "out" in let v := "v" in
    ("indirect_add_three'", ([out;a;b;c], [], bedrock_func_body:(
    stackalloc 4 as v {
      indirect_add(v, a, b);
      indirect_add(out, v, c)
    }
  ))).

  Instance spec_of_indirect_add_three' : spec_of "indirect_add_three'" :=
    fnspec! "indirect_add_three'" out a b c / vout va vb vc Ra Rb Rc R,
    { requires t m :=
        m =* cell_value out vout * R /\
        m =* cell_value a va * Ra /\
        m =* cell_value b vb * Rb /\
        m =* cell_value c vc * Rc;
      ensures t' m' := t = t' /\ m' =* cell_value out (g va vb vc) * R }. *)
End with_parameters.
