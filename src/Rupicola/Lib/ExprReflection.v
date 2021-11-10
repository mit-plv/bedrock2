From Rupicola Require Import Lib.Core Lib.Notations Lib.Tactics.

Module ExprReflection.
  Section with_parameters.
    Context {width: Z} {BW: Bitwidth width} {word: word.word width} {memT: map.map word Byte.byte}.
    Context {localsT: map.map String.string word}.
    Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
    Context {ext_spec: bedrock2.Semantics.ExtSpec}.
    Context {word_ok : word.ok word} {mem_ok : map.ok memT}.
    Context {locals_ok : map.ok localsT}.
    Context {env_ok : map.ok env}.
    Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

    Section Core.
      Class expr_denotation T :=
        { er_T2w: T -> word;
          er_default: T;
          er_op: Type;
          er_opfun: er_op -> T -> T -> T;
          er_opname: er_op -> bopname.bopname;
          er_opfun_morphism: forall op (x y: T),
              er_T2w ((er_opfun op) x y) =
              Semantics.interp_binop (er_opname op) (er_T2w x) (er_T2w y) }.

      Context {T} {er: expr_denotation T}.

      Inductive AST :=
      | ELit (z: Z) (t: T) (ok: word.of_Z z = er_T2w t)
      | EVar (nm: string)
      | EOp (op: er_op) (l r: AST).

      Context (locals: localsT)
              (concrete_locals: map.rep (map := SortedListString.map T)).

      Fixpoint interp ast :=
        match ast with
        | ELit z t _ => t
        | EVar nm => match map.get concrete_locals nm with
                    | Some v => v
                    | None => er_default
                    end
        | EOp op l r => (er_opfun op) (interp l) (interp r)
        end.

      Fixpoint compile ast :=
        match ast with
        | ELit z t _ => expr.literal z
        | EVar nm => expr.var nm
        | EOp op l r => expr.op (er_opname op) (compile l) (compile r)
        end.

      Definition is_some {A} (o: option A) :=
        if o then true else false.

      Fixpoint witness ast :=
        match ast with
        | ELit z t _ => True
        | EVar nm => map.get concrete_locals nm <> None
        | EOp op l r => witness r /\ witness l
        end.

      Fixpoint witnessb ast acc :=
        match ast with          (* FIXME use naive word representation for equality checks *)
        | ELit z t _ => acc
        | EVar nm => is_some (map.get concrete_locals nm) && acc
        | EOp op l r => witnessb r (witnessb l acc)
        end%bool.

      Lemma witnessb_decreasing ast :
        witnessb ast false = false.
      Proof.
        induction ast; cbn; intros; rewrite ?Bool.andb_false_r;
          congruence.
      Qed.

      Lemma witnessb_sound ast :
        witnessb ast true = true ->
        witness ast.
      Proof.
        induction ast; cbn; intros H; rewrite ?Bool.andb_true_r in H.
        - eauto.
        - destruct lookup; cbn in *; congruence.
        - destruct (witnessb ast1 true); [ solve [eauto] | ].
          rewrite witnessb_decreasing in H; discriminate.
      Qed.

      Lemma interp_sound' ast:
        forall (P: word -> Prop) mem,
          witness ast ->
          P (er_T2w (interp ast)) ->
          map.mapped_compat er_T2w concrete_locals locals ->
          WeakestPrecondition.expr mem locals (compile ast) P.
      Proof.
        induction ast; cbn -[map.get]; intros P mem Hw HP Heq.
        - destruct ok; red; unfold dlet; congruence.
        - specialize (Heq nm); destruct map.get.
          + red; eauto.
          + exfalso; apply Hw; reflexivity.
        - apply IHast1; intuition.
          apply IHast2; intuition.
          rewrite <- er_opfun_morphism.
          congruence.
      Qed.

      Lemma interp_sound ast mem:
        witnessb ast true = true ->
        map.mapped_compat er_T2w concrete_locals locals ->
        WeakestPrecondition.dexpr mem locals (compile ast) (er_T2w (interp ast)).
      Proof.
        intros; apply interp_sound'; eauto using witnessb_sound.
      Qed.

      Lemma interp_complete ast:
        forall (P: word -> Prop) mem,
          witness ast ->
          map.mapped_compat er_T2w concrete_locals locals ->
          WeakestPrecondition.expr mem locals (compile ast) P ->
          P (er_T2w (interp ast)).
      Proof.
        induction ast; cbn -[map.get]; intros P mem H Heq HP; red in HP.
        - destruct ok; unfold dlet in HP; congruence.
        - destruct HP as (x & Heq' & HP).
          destruct map.get eqn:?.
          + erewrite Heq in Heq' by eassumption.
            inversion Heq'; subst; eassumption.
          + exfalso. eapply H; reflexivity.
        - destruct H.
          rewrite er_opfun_morphism.
          eapply IHast2; intuition.
          eapply IHast1; intuition.
          eassumption.
      Qed.
    End Core.

    Instance expr_word_denotation : expr_denotation word :=
      {| er_T2w w := w;
         er_default := word.of_Z 0;
         er_op := bopname.bopname;
         er_opname op := op;
         er_opfun op :=
           match op with
           | bopname.add => word.add
           | bopname.sub => word.sub
           | bopname.mul => word.mul
           | bopname.mulhuu => word.mulhuu
           | bopname.divu => word.divu
           | bopname.remu => word.modu
           | bopname.and => word.and
           | bopname.or => word.or
           | bopname.xor => word.xor
           | bopname.sru => word.sru
           | bopname.slu => word.slu
           | bopname.srs => word.srs
           | bopname.lts => fun x y => word.b2w (word.lts x y)
           | bopname.ltu => fun x y => word.b2w (word.ltu x y)
           | bopname.eq => fun x y => word.b2w (word.eqb x y)
           end;
         er_opfun_morphism :=
           ltac:(destruct op; intros; cbn;
                repeat lazymatch goal with
                       | [  |- context[if ?x then _ else _] ] => destruct x
                       | _ => reflexivity
                       end) |}.

    Inductive ReifiedZOpp := RZ_add | RZ_sub | RZ_mul | RZ_land | RZ_lor | RZ_lxor.

    Instance expr_Z_denotation : expr_denotation Z :=
      {| er_T2w z := word.of_Z z;
         er_default := 0%Z;
         er_op := ReifiedZOpp;
         er_opname zop :=
           match zop with
           | RZ_add => bopname.add
           | RZ_sub => bopname.sub
           | RZ_mul => bopname.mul
           | RZ_land => bopname.and
           | RZ_lor => bopname.or
           | RZ_lxor => bopname.xor
           end;
         er_opfun zop :=
           match zop with
           | RZ_add => Z.add
           | RZ_sub => Z.sub
           | RZ_mul => Z.mul
           | RZ_land => Z.land
           | RZ_lor => Z.lor
           | RZ_lxor => Z.lxor
           end;
         er_opfun_morphism :=
           ltac:(destruct op; intros; cbn;
                eauto using word.morph_and, word.morph_or, word.morph_xor,
                word.ring_morph_add, word.ring_morph_mul, word.ring_morph_sub;
                reflexivity) |}.

    Lemma compile_expr {A} (to_W: A -> word)
          [tr mem locals functions] (a: A) (e: expr) :
      let v := a in
      forall {P} {pred: P v -> predicate}
        {k: nlet_eq_k P v} {k_impl}
        var,

        WeakestPrecondition.dexpr mem locals e (to_W v) ->

        (let v := v in
         <{ Trace := tr;
            Memory := mem;
            Locals := map.put locals var (to_W v);
            Functions := functions }>
         k_impl
         <{ pred (k v eq_refl) }>) ->

        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq (cmd.set var e) k_impl
        <{ pred (nlet_eq [var] v k) }>.
    Proof. repeat straightline; eauto. Qed.

    Definition compile_expr_w := compile_expr (fun w => w).
    Definition compile_expr_bool := compile_expr (fun b => word.b2w b).
    Definition compile_expr_byte := compile_expr (fun b => word_of_byte b).
    Definition compile_expr_nat := compile_expr (fun n => word.of_Z (Z.of_nat n)).
    Definition compile_expr_Z := compile_expr (fun z => word.of_Z z).
  End with_parameters.

  Ltac find_key_by_value bs v0 :=
    lazymatch bs with
    | [] => constr:(@None string)
    | (?k, ?v) :: ?bs =>
      lazymatch v with
      | v0 => constr:(Some k)
      | _ => find_key_by_value bs v0
      end
    end.

  Ltac expr_reify_word W bindings w :=
    let expr_reify_op nm l r :=
        let l := expr_reify_word W bindings l in
        let r := expr_reify_word W bindings r in
        constr:(EOp (word:=W) (er := expr_word_denotation) nm l r) in
    lazymatch w with (* FIXME add reification support for gt, ge, le, neg; also for Byte constants *)
    | word.add ?l ?r    => expr_reify_op bopname.add l r
    | word.sub ?l ?r    => expr_reify_op bopname.sub l r
    | word.mul ?l ?r    => expr_reify_op bopname.mul l r
    | word.mulhuu ?l ?r => expr_reify_op bopname.mulhuu l r
    | word.divu ?l ?r   => expr_reify_op bopname.divu l r
    | word.modu ?l ?r   => expr_reify_op bopname.remu l r
    | word.and ?l ?r    => expr_reify_op bopname.and l r
    | word.or ?l ?r     => expr_reify_op bopname.or l r
    | word.xor ?l ?r    => expr_reify_op bopname.xor l r
    | word.sru ?l ?r    => expr_reify_op bopname.sru l r
    | word.slu ?l ?r    => expr_reify_op bopname.slu l r
    | word.srs ?l ?r    => expr_reify_op bopname.srs l r
    | word.b2w (word.lts ?l ?r) => expr_reify_op bopname.lts l r
    | word.b2w (word.ltu ?l ?r) => expr_reify_op bopname.ltu l r
    | word.b2w (word.eqb ?l ?r) => expr_reify_op bopname.eq l r
    | _ =>
      lazymatch find_key_by_value bindings w with
      | Some ?k => constr:(EVar (word:=W) (er := expr_word_denotation) k)
      | None =>
        lazymatch w with
        | word.of_Z ?z =>
          constr:(ELit (word:=W) (er := expr_word_denotation)
                       z (word.of_Z z) eq_refl)
        | _ =>
          constr:(ELit (word:=W) (er := expr_word_denotation)
                       (word.unsigned w) w (word.of_Z_unsigned w))
        end
      end
    end.

  Ltac expr_reify_Z bindings z :=
    let expr_reify_op nm l r :=
        let l := expr_reify_Z bindings l in
        let r := expr_reify_Z bindings r in
        constr:(EOp (er := expr_Z_denotation) nm l r) in
    lazymatch z with
    | Z.add ?l ?r  => expr_reify_op RZ_add l r
    | Z.sub ?l ?r  => expr_reify_op RZ_sub l r
    | Z.mul ?l ?r  => expr_reify_op RZ_mul l r
    | Z.land ?l ?r => expr_reify_op RZ_land l r
    | Z.lor ?l ?r  => expr_reify_op RZ_lor l r
    | Z.lxor ?l ?r => expr_reify_op RZ_lxor l r
    | _ =>
      lazymatch find_key_by_value bindings z with
      | Some ?k => constr:(EVar (er := expr_Z_denotation) k)
      | None => constr:(ELit (er := expr_Z_denotation) z z eq_refl)
      end
    end.

  (* Swapping out the whole goal with `change` is more robust than swapping out
     just `val` with `change val with …` (the latter sometimes fails to find
     `val` in the goal). *)

  Ltac change_goal_change term :=
    change term.

  Ltac change_goal_replace term :=
    lazymatch goal with
    | [  |- ?g ] =>
      (* FIXME why is `by (vm_cast_no_check (@eq_refl Prop g))` slower? *)
      replace g with term by reflexivity
    end.

  Lemma change_goal {P Q: Prop} : Q = P -> P -> Q.
  Proof. intros -> ?; assumption. Qed.

  Ltac change_goal_refine term :=
    lazymatch goal with (* FIXME why is `@eq_refl Prop g <: g = term` slower? *)
    | [  |- ?g ] => simple refine (change_goal (@eq_refl Prop g : g = term) _)
    end.

  Ltac change_goal term :=
    (* `refine` is faster than `replace`, which is faster than `change` *)
    change_goal_refine term.

  Tactic Notation "_reify_change_dexpr"
         constr(mem) constr(locals) constr(expr)
         open_constr(reifier) constr(reified) constr(bindings) :=
    unify expr (compile reified);
    change_goal (WeakestPrecondition.dexpr
                   mem locals (compile reified)
                   (er_T2w (expr_denotation := reifier)
                           (interp (er := reifier)
                                   (map.of_list (map := SortedListString.map _) bindings)
                                   reified))).

  Ltac reify_change_dexpr_w :=
    lazymatch goal with
    | [  |- WeakestPrecondition.dexpr ?mem ?locals ?expr ?val ] =>
      lazymatch locals with
      | map.of_list ?bindings =>
        lazymatch type of val with
        | @word.rep _ ?W =>
          let reified := expr_reify_word W bindings val in
          _reify_change_dexpr mem locals expr expr_word_denotation reified bindings
        end
      | _ => fail 0 locals "is not a list of bindings"
      end
    | [  |- ?g ] => fail 0 g "is not a dexpr goal"
    end.

  Ltac zify_bindings bs :=
    lazymatch bs with
    | [] => constr:(@List.nil (string * Z))
    | (?k, ?w) :: ?tl =>
      let z := lazymatch w with
              | @word.of_Z _ _ ?z => constr:(z)
              | _                 => constr:(word.unsigned w)
              end in
      let tl := zify_bindings tl in
      constr:((k, z) :: tl)
    end.

  Ltac reify_change_dexpr_z :=
    lazymatch goal with
    | [  |- WeakestPrecondition.dexpr ?mem ?locals ?expr ?val ] =>
      lazymatch locals with
      | map.of_list ?bindings =>
        lazymatch val with
        | word.of_Z ?z =>
          let z_bindings := zify_bindings bindings in
          let z_bindings := type_term z_bindings in
          let reified := expr_reify_Z z_bindings z in
          _reify_change_dexpr mem locals expr expr_Z_denotation reified z_bindings
        end
      | _ => fail 0 locals "is not a list of bindings"
      end
    | [  |- ?g ] => fail 0 g "is not a dexpr goal"
    end.

  Ltac reify_change_dexpr_locals :=
    lazymatch goal with
    | [  |- WeakestPrecondition.dexpr _ ?locals _ _ ] =>
      let bindings := map_to_list locals in
      set_change locals with (map.of_list bindings)
    | [  |- ?g ] => fail 0 g "is not a dexpr goal"
    end.

  Ltac reify_change_dexpr :=
    lazymatch goal with
    | [  |- WeakestPrecondition.dexpr _ _ _ ?val ] =>
      reify_change_dexpr_locals;
      lazymatch val with
      | word.of_Z ?z => reify_change_dexpr_z
      | _ => reify_change_dexpr_w
      end
    | [  |- ?g ] => fail 0 g "is not a dexpr goal"
    end.

  Ltac compile_prove_reified_dexpr :=
    eapply interp_sound;
    [ reflexivity |
      eapply map.mapped_compat_of_list;
      lazymatch goal with
      | |- context[expr_Z_denotation] => (* LATER Use reification to speed up this rewrite *)
        cbv [List.map fst snd er_T2w expr_Z_denotation]; rewrite ?word.of_Z_unsigned
      | _ => idtac
      end; reflexivity
      | .. ].

  Ltac compile_let_as_expr :=
    lazymatch goal with
    | [ |- WP_nlet_eq ?v ] =>
      lazymatch type of v with
      | word.rep       => simple apply compile_expr_w
      | bool              => simple apply compile_expr_bool
      | Init.Byte.byte => simple apply compile_expr_byte
      | nat              => simple apply compile_expr_nat
      | Z              => simple apply compile_expr_Z
      | ?t             => fail "Unrecognized type" t
      end; cbv beta in *
    | [  |- ?g ] => fail 0 g "is not a Rupicola goal"
    end.
End ExprReflection.

Ltac compile_expr :=
  (* LATER: Consider clearing local hypotheses here, since large contexts make
     `apply` slow (but careful not to remove [map.ok]). *)
  ExprReflection.reify_change_dexpr;
  ExprReflection.compile_prove_reified_dexpr.

Ltac compile_assignment :=
  ExprReflection.compile_let_as_expr;
  [ ExprReflection.compile_expr | .. ].

(* For dexpr side conditions: *)
#[export] Hint Extern 8 (WeakestPrecondition.dexpr _ _ _ _) =>
  compile_expr : compiler_side_conditions.

(* For let-bound exprs: *)
#[export] Hint Extern 8 =>
  compile_assignment; shelve : compiler.
  (* Higher priority than compilation lemmas for individual operations *)

Section Tests.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}.
  Context {mem: map.map word Byte.byte} {locals: map.map String.string word}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.

  Context (m: mem).

  #[local] Notation dexpr m e x :=
    (WeakestPrecondition.dexpr (mem := mem) (locals := locals) map.empty m e x).

  Local Goal {e | forall z,
          dexpr #{ "z" => word.of_Z z }# e
                (word.of_Z (Z.land 3 z)) }.
  Proof. eexists; intros; compile_expr. Qed.

  Local Goal {e | forall w,
          dexpr #{ "w" => w }# e
                (word.and (word.of_Z 3) w) }.
  Proof. eexists; intros; compile_expr. Qed.

  Local Goal {e | forall b,
          dexpr #{ "b" => word_of_byte b }# e
                (word_of_byte (byte.and Byte.x03 b)) }.
  Proof. Fail eexists; intros; compile_expr. Abort. (* TODO *)

  Local Goal {e | forall b,
          dexpr #{ "b" => word.b2w b }# e
                (word.b2w (andb b false)) }.
  Proof. Fail eexists; intros; compile_expr. Abort. (* TODO *)

  Local Goal {e | forall x b,
          dexpr #{ "x" => word.of_Z x; "b" => word_of_byte b }# e
                (word.add (word.of_Z (Z.add x x))
                          (word_of_byte (byte.and b b))) }.
  Proof. Fail eexists; intros; compile_expr. Abort. (* TODO *)
End Tests.
