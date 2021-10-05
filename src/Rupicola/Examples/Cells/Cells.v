Require Import Rupicola.Lib.Api.

Record  cell {width: Z} {BW: Bitwidth width} {word: word.word width} := { data : word }.
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

  Definition cell_value (addr: word) (c: cell)
    : mem -> Prop :=
    scalar addr c.(data).

  Definition get c := c.(data).
  Definition put v := {| data := v |}.
  (* No reference to the original cell: Rupicola decides which one to modify
     based on the target of the call:
       let/n c := put x in …
             ^ .......^.... this gets mutated
                      ^ ... with this value *)

  Lemma compile_get : forall {tr mem locals functions} (c: cell),
    let v := get c in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
      R c_ptr c_var var,

      sep (cell_value c_ptr c) R mem ->
      map.get locals c_var = Some c_ptr ->

      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var v;
          Functions := functions }>
       k_impl
       <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.load access_size.word (expr.var c_var)))
              k_impl
      <{ pred (nlet_eq [var] v k) }>.
  Proof.
    intros.
    repeat straightline.
    exists (get c).
    split.
    { cbn.
      red.
      exists c_ptr.
      split.
      { eassumption. }
      { eexists; split; [ | reflexivity ].
        eapply load_word_of_sep.
        eassumption. } }
    red; intros.
    eassumption.
  Qed.

  Lemma compile_put : forall {tr mem locals functions} x,
    let v := put x in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
      R c_ptr _c c_var x_var,

      map.get locals x_var = Some x ->
      map.get locals c_var = Some c_ptr ->
      sep (cell_value c_ptr _c) R mem -> (* See FAQ on parameter order *)

      (let v := v in
       forall m,
         sep (cell_value c_ptr v) R m ->
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
      cmd.seq (cmd.store access_size.word (expr.var c_var) (expr.var x_var))
              k_impl
      <{ pred (nlet_eq [c_var] v k) }>.
  Proof.
    intros.
    unfold cell_value in *.
    repeat straightline.
    exists c_ptr; split; eexists; split; eauto.
    - repeat straightline; eexists; split; eauto.
    - repeat straightline; eauto.
  Qed.

  #[global] Program Instance SimpleAllocable_cell : Allocable cell_value :=
    {| size_in_bytes := Memory.bytes_per_word width;
       size_in_bytes_mod := Z_mod_same_full _;
       P_to_bytes := _;
       P_from_bytes := _ |}.
  Next Obligation.
    apply (P_to_bytes (Allocable := Allocable_scalar)).
  Qed.
  Next Obligation.
    intros m H.
    edestruct (P_from_bytes (Allocable := Allocable_scalar) _ _ H).
    exists {| data := x |}. assumption.
  Qed.
End with_parameters.

#[export] Hint Extern 1 => simple eapply compile_get; shelve : compiler.
#[export] Hint Extern 1 => simple eapply compile_put; shelve : compiler.
