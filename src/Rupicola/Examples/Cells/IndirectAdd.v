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

  Local Notation "m =* P" := (P%sep m) (at level 70, only parsing).

  Instance spec_of_indirect_add : spec_of "indirect_add" :=
    fnspec! "indirect_add" pa pb pc / a Ra b Rb c Rc,
    { requires t m :=
        m =* cell_value pa a * Ra /\ m =* cell_value pb b * Rb /\ m =* cell_value pc c * Rc;
      ensures t' m' :=
        t = t' /\ m' =* cell_value pa (indirect_add b c) * Ra }.

  Derive indirect_add_body SuchThat
         (defn! "indirect_add"("a", "b", "c") { indirect_add_body },
          implements indirect_add)
         As indirect_add_body_correct.
  Proof.
    compile.
  Qed.

  (* FIXME auto-generate lemma from pre-post condition pair? *)

  Lemma compile_indirect_add : forall {tr mem locals functions} a b c,
    let v := indirect_add b c in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
      va vb vc pa pb pc Ra Rb Rc,

      map.get locals va = Some pa ->
      (cell_value pa a ⋆ Ra) mem ->

      (cell_value pb b ⋆ Rb) mem ->
      map.get locals vb = Some pb ->

      (cell_value pc c ⋆ Rc) mem ->
      map.get locals vc = Some pc ->

      (_: spec_of "indirect_add") functions ->

      (let v := v in
       forall m,
         (* FIXME would like to prove this:
            (forall Ra, sep (cell_value pa a) Ra m ->
                        sep (cell_value pa v) Ra m) -> *)
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
    let/n a := indirect_add a b in
    let/n a := indirect_add a b in
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
    let/n a := indirect_add a b in
    let/n a := indirect_add a c in
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

  Require Import Rupicola.Lib.Alloc.

  Definition indirect_add_three' (a b c: cell) :=
    let/n v := alloc (indirect_add a b) in
    let/n out := indirect_add v c in
    out.

  Instance spec_of_indirect_add_three' : spec_of "indirect_add_three'" :=
    fnspec! "indirect_add_three'" pout pa pb pc / out a b c Ra Rb Rc R,
    { requires t m :=
        m =* cell_value pout out * R /\
        m =* cell_value pa a * Ra /\
        m =* cell_value pb b * Rb /\
        m =* cell_value pc c * Rc;
      ensures t' m' :=
        t = t' /\ m' =* cell_value pout (indirect_add_three' a b c) * R }.

  (* FIXME replace original compile_alloc with this. *)
  Lemma compile_alloc
        {tr m l functions A} (v : A):
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
           {I} {AP : I -> word.rep -> A -> map.rep -> Prop} `{@Allocable _ _ _ I A AP}
           out_var,

      (forall i out_ptr uninit m',
          (* There may be more than one predicate about m, and we're not sure
             yet which one to use; see FAQ. *)
         (forall (R: mem -> Prop), R m -> sep (AP i out_ptr uninit) R m') ->
         (<{ Trace := tr;
             Memory := m';
             Locals := map.put l out_var out_ptr;
             Functions := functions }>
          k_impl
          <{ pred_sep (Memory.anybytes out_ptr size_in_bytes) pred (nlet_eq [out_var] v k) }>)) ->
      <{ Trace := tr;
         Memory := m;
         Locals := l;
         Functions := functions }>
      cmd.stackalloc out_var size_in_bytes k_impl
      <{ pred (nlet_eq [out_var] (alloc v) k) }>.
  Proof.
    repeat straightline.
    split; eauto using size_in_bytes_mod.
    intros out_ptr mStack mCombined Hplace%P_from_bytes.
    destruct Hplace as [i [out Hout]].
    repeat straightline.
    specialize (H0 i out_ptr out mCombined).
    eapply WeakestPrecondition_weaken
      with (p1 := pred_sep (Memory.anybytes out_ptr size_in_bytes)
                           pred (let/n x as out_var eq:Heq := v in
                                 k x Heq)).
    2:{
      eapply H0.
      exists mStack; exists m;
        intuition.
      apply map.split_comm; eauto.
    }
    {
      clear H0.
      unfold pred_sep;
        unfold Basics.flip;
        simpl.
      intros.
      destruct H0 as [mem1 [mem2 ?]].
      exists mem2; exists mem1;
        intuition.
      apply map.split_comm; eauto.
    }
  Qed.

  Ltac cleanup_alloc :=
    intros;
    repeat match goal with
           | [ H: ?R ?m, H': (forall R, R ?m -> _ ?m') |-
               WeakestPrecondition.cmd ?_call ?_impl ?_tr ?m' ?_locals ?_post ] =>
             apply H' in H; change (fun x => ?h x) with h in H
           | [ m: mem, m': mem |- _ ] =>
             match goal with
             | [ H: forall R, R m -> _ m' |- _ ] => clear H
             end
           end.

  Hint Extern 0 => simple eapply compile_alloc; cleanup_alloc; shelve.

  Open Scope Z_scope.

  (* FIXME (dustin): Replace Allocable with this? *)
  Class Allocable {A} (P : word.rep -> A -> mem -> Prop) :=
    { size_in_bytes : Z;
      size_in_bytes_mod :
        size_in_bytes mod Memory.bytes_per_word width = 0;
      P_to_bytes px x :
        Lift1Prop.impl1 (P px x) (Memory.anybytes px size_in_bytes);
      P_from_bytes px :
        Lift1Prop.impl1 (Memory.anybytes px size_in_bytes)
                        (Lift1Prop.ex1 (P px)) }.

  Instance Allocable_of_IAllocable {A} (P : word.rep -> A -> mem -> Prop)
           {H: Allocable P} : Alloc.Allocable (fun _: unit => P).
  Proof.
    refine {| Alloc.size_in_bytes := size_in_bytes;
              Alloc.size_in_bytes_mod := size_in_bytes_mod;
              Alloc.P_to_bytes := _;
              Alloc.P_from_bytes := _ |}; intros.
    - apply P_to_bytes.
    - abstract (red; exists tt; apply P_from_bytes; assumption).
  Defined.

  (* FIXME move *)
  Lemma bytes_per_width_bytes_per_word : forall width,
      width >= 0 ->
      Z.of_nat (Memory.bytes_per (width := width) access_size.word) = Memory.bytes_per_word width.
  Proof.
    intros; unfold Memory.bytes_per, Memory.bytes_per_word.
    rewrite Z2Nat.id; try apply Z.div_pos; lia.
  Qed.

  Lemma bytes_per_wordwidth_bytes_per_word :
      Z.of_nat (Memory.bytes_per (width := width) access_size.word) = Memory.bytes_per_word width.
  Proof.
    apply bytes_per_width_bytes_per_word.
    pose proof word.width_pos; lia.
  Qed.

  Lemma split_bytes_per_word:
    forall x : word,
      Z.of_nat
        (Datatypes.length
           (HList.tuple.to_list
              (LittleEndian.split (Memory.bytes_per (width := width) access_size.word)
                                  (word.unsigned x)))) = Memory.bytes_per_word width.
  Proof.
    intros x.
    rewrite HList.tuple.length_to_list.
    apply bytes_per_wordwidth_bytes_per_word.
  Qed.

  Lemma word_width_round :
      width = 8 * ((width + 7) / 8).
  Proof. destruct width_cases; subst; reflexivity. Qed.

  Program Instance Allocable_scalar : Allocable scalar :=
    {| size_in_bytes := Memory.bytes_per_word width;
       size_in_bytes_mod := Z_mod_same_full _;
       P_to_bytes := _;
       P_from_bytes := _ |}.
  Next Obligation.
    intros m Hm.
    evar (bs: list byte);
      assert (array ptsto (word.of_Z 1) px bs m) by (subst bs; apply Hm).
    subst bs; erewrite <- split_bytes_per_word.
    eapply array_1_to_anybytes; eauto.
  Qed.
  Next Obligation.
    intros m Hm.
    eapply anybytes_to_array_1 in Hm; destruct Hm as (bs & Harray & Hlen).
    eexists.
    eapply scalar_of_bytes in Harray; try eassumption.
    2: rewrite Hlen.
    all: destruct width_cases; subst; reflexivity || lia.
  Qed.

  Program Instance Allocable_cell : Allocable cell_value :=
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

  Derive indirect_add_three'_body SuchThat
         (defn! "indirect_add_three'"("out", "a", "b", "c") { indirect_add_three'_body },
          implements indirect_add_three' using ["indirect_add"])
    As indirect_add_three'_body_correct.
  Proof.
    compile_setup.
    compile_step.
    compile_step.
    compile_step.
    eapply compile_nlet_as_nlet_eq.
    simple eapply compile_alloc; cleanup_alloc.
    (* FIXME when no instance is defined the typeclass goal is shelved; why? *)
    compile_step.
    compile_step.
    compile_step.
    compile_step.
    compile_step.
    compile_step.
    compile_step.
    compile_step.
    compile_step.
    compile_step.
    compile_step.
    compile_step.
    compile_step.
    (* FIXME at this point we've lost too much info: we lost most clauses that
       talked about `m'`.  The problem is that the compilation lemmas assume
       there's a single relevant clause.  Is this worth a refactoring so that we
       propagate info about all statements about a given memory? *)
  Abort.
End with_parameters.
