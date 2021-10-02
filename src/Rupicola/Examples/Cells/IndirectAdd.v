(** A Rupicola version of the indirect_add example in Bedrock2. **)
Require Import Coq.Classes.Morphisms.

Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.Cells.Cells.
Require Import Rupicola.Lib.Alloc.

Require Import coqutil.Decidable.
Require Import bedrock2.Lift1Prop.

Section Unsep.
  Context {key value : Type} {map : map.map key value}.

  Definition pure (P: Prop) := (fun m: map => P).

  (* FIXME shouldn't *this* be the definition of `and1`? *)
  Definition unsep (p q: map -> Prop) : map -> Prop :=
    fun m => p m /\ q m.

  Fixpoint unseps (props: list (map -> Prop)) : map -> Prop :=
    match props with
    | [] => pure True
    | [prop] => prop
    | prop :: props => unsep prop (unseps props)
    end.

  Global Instance Proper_iff1_unsep :
    Proper (iff1 ==> iff1 ==> iff1) unsep.
  Proof. firstorder idtac. Qed.

  Global Instance Proper_impl1_unsep :
    Proper (impl1 ==> impl1 ==> impl1) unsep.
  Proof. firstorder idtac. Qed.

  Lemma unsep_assoc (p q r: map -> Prop) :
    iff1 (unsep (unsep p q) r) (unsep p (unsep q r)).
  Proof. firstorder idtac. Qed.

  Lemma unsep_pure_True_l P :
    iff1 (unsep (pure True) P) P.
  Proof. firstorder idtac. Qed.

  Lemma unsep_pure_True_r P :
    iff1 (unsep P (pure True)) P.
  Proof. firstorder idtac. Qed.

  Lemma unsep_pure_False_l P :
    iff1 (unsep (pure False) P) (pure False).
  Proof. firstorder idtac. Qed.

  Lemma unsep_pure_False_r P :
    iff1 (unsep P (pure False)) (pure False).
  Proof. firstorder idtac. Qed.

  Lemma sep_pure_False_l P :
    iff1 (sep (pure False) P) (pure False).
  Proof. firstorder idtac. Qed.

  Lemma sep_pure_False_r P :
    iff1 (sep P (pure False)) (pure False).
  Proof. firstorder idtac. Qed.

  Lemma impl1_pure_False_l P :
    impl1 (pure False) P.
  Proof. firstorder idtac. Qed.

  Lemma impl1_pure_True_r P :
    impl1 P (pure True).
  Proof. firstorder idtac. Qed.

  Lemma unsep_distr_sep_l: (* FIXME: this is sep_and_r_fwd *)
    forall p1 p2 p3 : map -> Prop,
      impl1 (p1 ⋆ unsep p2 p3) (unsep (p1 ⋆ p2) (p1 ⋆ p3)).
  Proof. firstorder idtac. Qed.

  Lemma unsep_distr_sep_r: (* FIXME: this is sep_and_l_fwd *)
    forall p1 p2 p3 : map -> Prop,
      impl1 (unsep p1 p2 ⋆ p3) (unsep (p1 ⋆ p3) (p2 ⋆ p3)).
  Proof. firstorder idtac. Qed.

  Lemma unseps_distr_sep_l :
    forall p1 ps2,
      impl1 (p1 ⋆ unseps ps2) (unseps (List.map (sep p1) ps2)).
  Proof.
    induction ps2 as [| p2 [|] IHps2]; simpl in *; intros.
    - apply impl1_pure_True_r.
    - reflexivity.
    - rewrite <- IHps2, unsep_distr_sep_l; reflexivity.
  Qed.

  Lemma unseps_distr_sep_r :
    forall ps1 p2,
      impl1 (unseps ps1 ⋆ p2) (unseps (List.map (fun p1 => sep p1 p2) ps1)).
  Proof.
    induction ps1 as [| p1 [|] IHps1]; simpl in *; intros.
    - apply impl1_pure_True_r.
    - reflexivity.
    - rewrite <- IHps1, unsep_distr_sep_r; reflexivity.
  Qed.

  Lemma unseps_map_impl1_ext (f g: (map -> Prop) -> (map -> Prop))
        (H: forall p, impl1 (f p) (g p)) :
    forall ps, impl1 (unseps (List.map f ps)) (unseps (List.map g ps)).
  Proof.
    induction ps as [| p [|] IHps]; simpl in *; intros.
    - reflexivity.
    - eauto.
    - rewrite IHps, H; reflexivity.
  Qed.

  Lemma unseps_app :
    forall es1 es2,
      iff1 (unseps (es1 ++ es2))
           (unsep (unseps es1) (unseps es2)).
  Proof.
    induction es1 as [| e1 [|] IHes1]; simpl in *; intros.
    - rewrite unsep_pure_True_l; reflexivity.
    - destruct es2; simpl.
      + rewrite unsep_pure_True_r; reflexivity.
      + reflexivity.
    - rewrite IHes1, unsep_assoc.
      reflexivity.
  Qed.

  Definition product {A B} (As: list A) (Bs: list B) : list (A * B) :=
    flat_map (fun a1 => List.map (pair a1) Bs) As.

  Definition map2 {A B C} (f: A -> B -> C) (ABs: list (A * B)) : list C :=
    List.map (fun ab => f (fst ab) (snd ab)) ABs.

  Lemma map2_map {A B C D} (f: B -> C -> D) (g: A -> B * C) (As: list A) :
    map2 f (List.map g As) =
    List.map (fun a => f (fst (g a)) (snd (g a))) As.
  Proof. unfold map2; rewrite map_map; reflexivity. Qed.

  Lemma map_map2 {A B C D} (f: A -> B -> C) (g: C -> D) (ABs: list (A * B)) :
    List.map g (map2 f ABs) =
    map2 (fun a b => g (f a b)) ABs.
  Proof. unfold map2; rewrite map_map; reflexivity. Qed.

  Lemma map2_map2 {A1 A2 B1 B2 C}
        (f: A1 -> A2 -> (B1 * B2))
        (g: B1 -> B2 -> C) (As: list (A1 * A2)) :
    map2 g (map2 f As) =
    map2 (fun a1 a2 => g (fst (f a1 a2)) (snd (f a1 a2))) As.
  Proof. unfold map2; rewrite map_map; reflexivity. Qed.

  Lemma map2_product {A B C} (f: A -> B -> C) (As: list A) (Bs: list B) :
    map2 f (product As Bs) =
    flat_map (fun a1 => List.map (f a1) Bs) As.
  Proof.
    unfold map2, product.
    rewrite !flat_map_concat_map, !concat_map, !map_map.
    f_equal; apply map_ext; intros; rewrite !map_map; reflexivity.
  Qed.

  Lemma unseps_distr_sep:
    forall ps1 ps2,
      impl1 (unseps ps1 ⋆ unseps ps2)
            (unseps (map2 sep (product ps1 ps2))).
  Proof.
    intros; rewrite map2_product; revert ps2.
    induction ps1 as [| p1 [|] IHps1]; simpl in *; intros.
    - apply impl1_pure_True_r.
    - rewrite app_nil_r.
      apply unseps_distr_sep_l.
    - rewrite unsep_distr_sep_r, unseps_app.
      rewrite <- IHps1.
      rewrite <- unseps_distr_sep_l.
      reflexivity.
  Qed.
End Unsep.

(* FIXME: unsep is just Lift1Prop.and1 *)

Module Reification.

Section Reification.
  Context {key value} {map : map.map key value} {map_ok : map.ok map}.
  Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.

  Notation unseps := (unseps (map := map)).

  Inductive expr :=
    | Pred (p: map -> Prop)
    | Sep (s1 s2: expr)
    | Unsep (s1 s2: expr).

  Fixpoint denote (e: expr) : map -> Prop :=
    match e with
    | Pred p => p
    | Sep s1 s2 => sep (denote s1) (denote s2)
    | Unsep s1 s2 => unsep (denote s1) (denote s2)
    end.

  Fixpoint unsep_normal_form' (e: expr) : list expr :=
    match e with
    | Pred p => [Pred p]
    | Sep s1 s2 =>
      map2 Sep (product (unsep_normal_form' s1)
                        (unsep_normal_form' s2))
    | Unsep s1 s2 =>
      unsep_normal_form' s1 ++ unsep_normal_form' s2
    end.

  Fixpoint Unseps (es: list expr) :=
    match es with
    | [] => Pred (pure True)
    | [e] => e
    | e :: es => Unsep e (Unseps es)
    end.

  Definition unsep_normal_form (e: expr) :=
    Unseps (unsep_normal_form' e).

  Lemma denote_Unseps :
    forall es, denote (Unseps es) = unseps (List.map denote es).
  Proof.
    induction es as [| e [|] IHes]; simpl in *; congruence.
  Qed.

  Lemma product_map {A B A' B'} (fA: A -> A') (fB: B -> B'):
    forall As Bs,
      product (List.map fA As) (List.map fB Bs) =
      map2 (fun a b => (fA a, fB b)) (product As Bs).
  Proof.
    unfold map2, product; intros.
    rewrite !flat_map_concat_map, !concat_map, !map_map.
    f_equal; apply map_ext; intros; rewrite !map_map.
    reflexivity.
  Qed.

  Lemma denote_map2_Sep :
    forall es1 es2,
      List.map denote (map2 Sep (product es1 es2)) =
      map2 sep (product (List.map denote es1)
                        (List.map denote es2)).
  Proof.
    intros.
    rewrite product_map, map2_map2, map_map2.
    reflexivity.
  Qed.

  Lemma unsep_normal_form_sound :
    forall e, impl1 (denote e) (denote (unsep_normal_form e)).
  Proof.
    unfold unsep_normal_form; induction e; simpl; intros;
      rewrite ?IHe1, ?IHe2, ?denote_Unseps, ?denote_map2_Sep, ?unseps_distr_sep, ?map_app, ?unseps_app in *; reflexivity.
  Qed.
End Reification.

  Ltac reify e :=
    let rec loop e :=
        match e with
        | sep ?s1 ?s2 =>
          let ur1 := loop s1 in let ur2 := loop s2 in uconstr:(Sep ur1 ur2)
        | unsep ?s1 ?s2 =>
          let ur1 := loop s1 in let ur2 := loop s2 in uconstr:(Unsep ur1 ur2)
        | ?p => uconstr:(Pred p)
        end in
    let ur := loop e in
    type_term ur.
End Reification.

Module Tactics.
  Ltac decompose_one_unsep H :=
    unfold unsep in H; cbv beta in H; decompose [and] H; clear H.

  Ltac decompose_all_unsep :=
    repeat match goal with
           | [ H: (unsep _ _) ?m |- _ ] => decompose_one_unsep H
           end.

  Ltac decompose_relevant_unsep :=
    repeat match goal with
           | [ H: (unsep _ _) ?m |- (sep _ _) ?m ] => decompose_one_unsep H
           end.

  Ltac normalize_relevant_sep :=
    match goal with
    | [ H: ?P ?m |- (sep _ _) ?m ] =>
      match P with
      | context[unsep] => (* FIXME check that progress works here *)
        let r := Reification.reify P in
        change P with (Reification.denote r) in H;
        apply Reification.unsep_normal_form_sound in H;
        simpl in H (* FIXME *);
        lazymatch type of H with
        | P m => fail "No progress"
        | _ => idtac
        end
      end
    end.
End Tactics.

Export Tactics.

Infix "&&&" := unsep (at level 50).

Hint Extern 1 ((sep _ _) _) => decompose_relevant_unsep; shelve : compiler_side_conditions.
Hint Extern 1 ((sep _ _) _) => normalize_relevant_sep; shelve : compiler_side_conditions.

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
    unfold unsep.
    repeat straightline.
    repeat (eexists; split; eauto).
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

  Derive indirect_add_three_body SuchThat
         (defn! "indirect_add_three"("a", "b", "c") { indirect_add_three_body },
          implements indirect_add_three using ["indirect_add"])
         As indirect_add_three_body_correct.
  Proof.
    compile.
  Qed.

  (* FIXME replace original compile_alloc with this?  The difference between the
     two lemmas is that this one allows learning the impact of stack allocation
     on more than one predicate: if the context contains `R1 m` and `R2 m`, this
     lemmas lets you learn both `anybytes ptr * R1` and `anybytes ptr * R2`,
     whereas the original one only lets you learn one of `anybytes ptr * R1` and
     `anybytes ptr * R2`.

     The problem is that although we *can* prove this more powerful lemma for
     this particular case (stack allocation), we can't do the same for other
     lemmas (try doing it above for `compile_indirect_add`, for example).

     The more robust approach is to package all facts already known together
     into a single one and *then* call a regular lemma that assumes a single
     fact.

     For example, here, we'd generate `(fun m => R1 m /\ R2 m) m`, and the usual
     `compile_alloc` would yield `(anybytes ptr * (fun m => R1 m /\ R2 m)) m`.
     From that it's then possible to derive the two facts that we wanted:
     `anybytes ptr * R1` and `anybytes ptr * R2`. *)
  Lemma compile_alloc'
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

  Ltac cleanup_alloc' :=
    (** Specialize the separation hypothesis created by `cleanup_alloc'`.

        Using the `cleanup_alloc'` lemma generates a hypothesis `H` of the form
        `forall R, R m -> anybytes ptr * R m`.  This tactic specializes that
        hypothesis using all `?R m` facts in the context, then clears `H`. **)
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

  Definition indirect_add_three' (a b c: cell) :=
    let/n v := alloc (indirect_add a b) in
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

  Derive indirect_add_three'_body SuchThat
         (defn! "indirect_add_three'"("out", "a", "b", "c") { indirect_add_three'_body },
          implements indirect_add_three' using ["indirect_add"])
    As indirect_add_three'_body_correct.
  Proof.
    compile.
    (* FIXME when no instance is defined the typeclass goal is shelved; why? *)
    (* FIXME the unit is shelved *)
    eexists; repeat compile_step.
    Grab Existential Variables.
    exact tt.
  Qed.
End with_parameters.
