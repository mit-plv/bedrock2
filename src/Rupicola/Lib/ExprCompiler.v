From Rupicola Require Import Lib.Core Lib.Notations Lib.Tactics.

#[local] Notation of_Z z := (word.of_Z z).
#[local] Notation of_N n := (word.of_Z (Z.of_N n)).
#[local] Notation of_nat n := (word.of_Z (Z.of_nat n)).
#[local] Notation of_byte n := (word.of_Z (byte.unsigned n)).
#[local] Notation of_bool b := (word.b2w b).

Section ExprCompiler.
  Context {width: Z} {BW: Bitwidth width}.
  Context {word: word.word width} {word_ok : word.ok word}.
  Context {mem: map.map word Byte.byte} {mem_ok : map.ok mem}.
  Context {locals: map.map String.string word} {locals_ok : map.ok locals}.
  Context {env: map.map string (list string * list string * cmd)}.

  (* Notation "<{ 'Memory' := m ; 'Locals' := l }> e ~> w" := *)
  (*   (WeakestPrecondition.dexpr (word := word) (mem := mem) (locals := locals) m l e w) *)
  (*     (at level 0, *)
  (*       format "'[v' <{  '[hv' 'Memory'  :=  '[hv' m ']' ; '//'  'Locals'  :=  '[hv' l ']' ']'  }> '//' e  '~>'  '[hv' w ']' ']'"). *)

  (* Notation "<{{ m ; l }}> e <{ w }>" := *)
  (*   (WeakestPrecondition.dexpr (word := word) (mem := mem) (locals := locals) m l e w) *)
  (*     (at level 0, *)
  (*       format "'[hv' <{{  '[' '[hv' m ']' ; '//'  '[hv' l ']' ']'  }}> '//'  e '//' <{  '[hv' w ']'  }> ']'"). *)

  Context {m: mem} {l: locals}.

  Notation DEXPR :=
    (WeakestPrecondition.dexpr (word := word) (mem := mem) (locals := locals) m).

  Notation DX := (DEXPR l).

  Ltac cleanup :=
    repeat straightline;
    repeat simple eapply WeakestPrecondition_dexpr_expr; eauto.

  Section Literals.
    Lemma expr_compile_Z_literal z : DX (expr.literal z) (of_Z z).
    Proof. cleanup. Qed.
    Lemma expr_compile_word_literal w : DX (expr.literal (word.unsigned w)) w.
    Proof. cleanup; symmetry; apply word.of_Z_unsigned. Qed.
  End Literals.

  Section Variables.
    Lemma expr_compile_var s w (h: map.get l s = Some w) : DX (expr.var s) w.
    Proof. cleanup. Qed.

    Lemma expr_compile_var_assoc {bs} s w (h: map.list_assoc_str s bs = Some w) :
      DEXPR (map.of_list bs) (expr.var s) w.
    Proof. cleanup. eauto using map.get_of_str_list_assoc_impl. Qed.
  End Variables.

  Section w_bop.
    Context (w1 w2: word) (e1 e2: expr).

    Hypothesis (H1: DX e1 w1).
    Hypothesis (H2: DX e2 w2).

    Local Lemma expr_compile_word_bop {bop}:
      DX (expr.op bop e1 e2) (Semantics.interp_binop bop w1 w2).
    Proof. cleanup. Qed.

    Notation DOP op w := (DX (expr.op op e1 e2) w).

    Definition expr_compile_word_add : DOP bopname.add (word.add w1 w2) := expr_compile_word_bop.
    Definition expr_compile_word_sub : DOP bopname.sub (word.sub w1 w2) := expr_compile_word_bop.
    Definition expr_compile_word_mul : DOP bopname.mul (word.mul w1 w2) := expr_compile_word_bop.
    Definition expr_compile_word_mulhuu : DOP bopname.mulhuu (word.mulhuu w1 w2) := expr_compile_word_bop.
    Definition expr_compile_word_divu : DOP bopname.divu (word.divu w1 w2) := expr_compile_word_bop.
    Definition expr_compile_word_modu : DOP bopname.remu (word.modu w1 w2) := expr_compile_word_bop.
    Definition expr_compile_word_and : DOP bopname.and (word.and w1 w2) := expr_compile_word_bop.
    Definition expr_compile_word_or : DOP bopname.or (word.or w1 w2) := expr_compile_word_bop.
    Definition expr_compile_word_xor : DOP bopname.xor (word.xor w1 w2) := expr_compile_word_bop.
    Definition expr_compile_word_sru : DOP bopname.sru (word.sru w1 w2) := expr_compile_word_bop.
    Definition expr_compile_word_slu : DOP bopname.slu (word.slu w1 w2) := expr_compile_word_bop.
    Definition expr_compile_word_srs : DOP bopname.srs (word.srs w1 w2) := expr_compile_word_bop.

    Lemma b2w_if (b: bool) :
      word.b2w (word := word) b = if b then word.of_Z 1 else word.of_Z 0.
    Proof. destruct b; reflexivity. Qed.

    Definition expr_compile_word_lts : DOP bopname.lts (of_bool (word.lts w1 w2)).
    Proof. rewrite b2w_if; eapply (@expr_compile_word_bop bopname.lts). Qed.
    Definition expr_compile_word_ltu : DOP bopname.ltu (of_bool (word.ltu w1 w2)).
    Proof. rewrite b2w_if; eapply (@expr_compile_word_bop bopname.ltu). Qed.
    Definition expr_compile_word_eqb : DOP bopname.eq (of_bool (word.eqb w1 w2)).
    Proof. rewrite b2w_if; eapply (@expr_compile_word_bop bopname.eq). Qed.
  End w_bop.

  (* TODO add other operators: not, les, leu, gts, gtu *)

  Section Z_bop.
    Context (z1 z2: Z) (e1 e2: expr).

    Notation to_w z := (of_Z z).

    Hypothesis (H1: DX e1 (to_w z1)).
    Hypothesis (H2: DX e2 (to_w z2)).

    Notation DOP op w := (DX (expr.op op e1 e2) w).

    Lemma expr_compile_Z_add : DOP bopname.add (to_w (Z.add z1 z2)).
    Proof. rewrite word.ring_morph_add; eauto using expr_compile_word_add. Qed.
    Lemma expr_compile_Z_sub : DOP bopname.sub (to_w (Z.sub z1 z2)).
    Proof. rewrite word.ring_morph_sub; eauto using expr_compile_word_sub. Qed.
    Lemma expr_compile_Z_mul : DOP bopname.mul (to_w (Z.mul z1 z2)).
    Proof. rewrite word.ring_morph_mul; eauto using expr_compile_word_mul. Qed.

    Lemma expr_compile_Z_land : DOP bopname.and (to_w (Z.land z1 z2)).
    Proof. rewrite word.morph_and; eauto using expr_compile_word_and. Qed.
    Lemma expr_compile_Z_lor : DOP bopname.or (to_w (Z.lor z1 z2)).
    Proof. rewrite word.morph_or; eauto using expr_compile_word_or. Qed.
    Lemma expr_compile_Z_lxor : DOP bopname.xor (to_w (Z.lxor z1 z2)).
    Proof. rewrite word.morph_xor; eauto using expr_compile_word_xor. Qed.
    Lemma expr_compile_Z_shiftl (h2: 0 <= z2 < width) :
      DOP bopname.slu (to_w (Z.shiftl z1 z2)).
    Proof. rewrite word.morph_shiftl; eauto using expr_compile_word_slu. Qed.
    Lemma expr_compile_Z_shiftr (h1: 0 <= z1 < 2 ^ width) (h2: 0 <= z2 < width) :
      DOP bopname.sru (to_w (Z.shiftr z1 z2)).
    Proof. rewrite word.morph_shiftr; eauto using expr_compile_word_sru. Qed.
  End Z_bop.

  Section N_bop.
    Context (n1 n2: N) (e1 e2: expr).

    Notation to_w z := (of_N z).

    Hypothesis (H1: DX e1 (to_w n1)).
    Hypothesis (H2: DX e2 (to_w n2)).

    Notation DOP op w := (DX (expr.op op e1 e2) w).

    Lemma expr_compile_N_add : DOP bopname.add (to_w (N.add n1 n2)).
    Proof. rewrite N2Z.inj_add; eauto using expr_compile_Z_add. Qed.
    Lemma expr_compile_N_sub (h: N.le n2 n1) : DOP bopname.sub (to_w (N.sub n1 n2)).
    Proof. rewrite N2Z.inj_sub; eauto using expr_compile_Z_sub. Qed.
    Lemma expr_compile_N_mul : DOP bopname.mul (to_w (N.mul n1 n2)).
    Proof. rewrite N2Z.inj_mul; eauto using expr_compile_Z_mul. Qed.
  End N_bop.

  Section nat_bop.
    Context (n1 n2: nat) (e1 e2: expr).

    Notation to_w n := (of_nat n).

    Hypothesis (H1: DX e1 (to_w n1)).
    Hypothesis (H2: DX e2 (to_w n2)).

    Notation DOP op w := (DX (expr.op op e1 e2) w).

    Lemma expr_compile_nat_add : DOP bopname.add (to_w (Nat.add n1 n2)).
    Proof. intros; rewrite Nat2Z.inj_add; eauto using expr_compile_Z_add. Qed.
    Lemma expr_compile_nat_sub :
      (n2 <= n1)%nat -> DOP bopname.sub (to_w (Nat.sub n1 n2)).
    Proof. intros; rewrite Nat2Z.inj_sub; eauto using expr_compile_Z_sub. Qed.
    Lemma expr_compile_nat_mul : DOP bopname.mul (to_w (Nat.mul n1 n2)).
    Proof. intros; rewrite Nat2Z.inj_mul; eauto using expr_compile_Z_mul. Qed.
  End nat_bop.

  Section byte_bop.
    Context (b1 b2: byte) (e1 e2: expr).
    Notation to_w b := (of_byte b).

    Hypothesis (H1: DX e1 (to_w b1)).
    Hypothesis (H2: DX e2 (to_w b2)).

    Notation DOP op w := (DX (expr.op op e1 e2) w).

    Lemma expr_compile_byte_and : DOP bopname.and (to_w (byte.and b1 b2)).
    Proof. cleanup; apply byte_morph_and. Qed.
    Lemma expr_compile_byte_xor : DOP bopname.xor (to_w (byte.xor b1 b2)).
    Proof. cleanup; apply byte_morph_xor. Qed.
  End byte_bop.

  Section bool_bop.
    Context (b1 b2: bool) (e1 e2: expr).
    Notation to_w b := (of_bool b).

    Hypothesis (H1: DX e1 (to_w b1)).
    Hypothesis (H2: DX e2 (to_w b2)).

    Notation DOP op w := (DX (expr.op op e1 e2) w).

    Ltac cleanup_bool lemma :=
      cleanup; rewrite !b2w_if; destruct b1, b2; simpl;
      rewrite <- lemma; reflexivity.

    Lemma expr_compile_bool_andb : DOP bopname.and (to_w (andb b1 b2)).
    Proof. cleanup_bool word.morph_and. Qed.
    Lemma expr_compile_bool_orb : DOP bopname.or (to_w (orb b1 b2)).
    Proof. cleanup_bool word.morph_or. Qed.
    Lemma expr_compile_bool_xorb : DOP bopname.xor (to_w (xorb b1 b2)).
    Proof. cleanup_bool word.morph_xor. Qed.
  End bool_bop.


  Section Assignments.
    Context {ext_spec: bedrock2.Semantics.ExtSpec}.
    Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

    Lemma compile_expr {A} (to_W: A -> word):
      forall [tr mem locals functions] (a: A) (e: expr),
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
    Definition compile_expr_Z := compile_expr (fun z => of_Z z).
    Definition compile_expr_N := compile_expr (fun n => of_N n).
    Definition compile_expr_nat := compile_expr (fun n => of_nat n).
    Definition compile_expr_byte := compile_expr (fun b => of_byte b).
    Definition compile_expr_bool := compile_expr (fun b => of_bool b).
  End Assignments.
End ExprCompiler.

Notation DEXPR := WeakestPrecondition.dexpr.

Ltac find_key_by_value bs v0 :=
  lazymatch bs with
  | [] => constr:(@None string)
  | (?k, ?v) :: ?bs =>
      lazymatch v with
      | v0 => constr:(Some k)
      | _ => find_key_by_value bs v0
      end
  end.

Ltac reify_change_dexpr_locals :=
  lazymatch goal with
  | [  |- DEXPR _ ?locals _ _ ] =>
      lazymatch locals with
      | map.of_list _ => fail 0 "Already reified"
      | _ =>
          let bindings := map_to_list locals in
          set_change locals with (map.of_list bindings)
      end
  | [  |- ?g ] => fail 0 g "is not a dexpr goal"
  end.

Ltac expr_compile_var :=
  lazymatch goal with
  | [ |- DEXPR _ (map.of_list ?bs) _ ?w ] =>
      lazymatch find_key_by_value bs w with
      | Some ?k =>
          simple eapply (expr_compile_var_assoc k w); reflexivity
      | None => fail "Not a variable"
      end
  | [  |- ?g ] => fail 0 g "is not a dexpr goal"
  end.

Ltac compile_let_as_expr :=
  lazymatch goal with
  | [ |- WP_nlet_eq ?v ] =>
    lazymatch type of v with
    | word.rep       => simple apply compile_expr_w
    | Z              => simple apply compile_expr_Z
    | N              => simple apply compile_expr_N
    | nat              => simple apply compile_expr_nat
    | Init.Byte.byte => simple apply compile_expr_byte
    | bool              => simple apply compile_expr_bool
    | ?t             => fail "[compile_let_as_expr]: Unrecognized type" t
    end; cbv beta in *
  | [  |- ?g ] => fail 0 g "is not a Rupicola goal"
  end.

Ltac compile_expr_step :=
  progress unshelve (typeclasses eauto 10 with expr_compiler); shelve_unifiable.

Ltac compile_expr :=
  (* LATER: Consider clearing local hypotheses here, since large contexts make
     `apply` slow (but careful not to remove [map.ok]). *)
  repeat compile_expr_step.

Ltac compile_assignment :=
  compile_let_as_expr; compile_expr.

Create HintDb expr_compiler.

(* For let-bound exprs: *)
#[export] Hint Extern 8 =>
  compile_assignment; shelve : compiler.
(* Higher priority than compilation lemmas for individual operations *)

(* For dexpr side conditions: *)
#[export] Hint Extern 8 (DEXPR _ _ _ _) =>
  compile_expr : compiler_side_conditions.

(* For variables *)
#[export] Hint Extern 7 =>
  expr_compile_var : expr_compiler.

(* Initial setup *)
#[export] Hint Extern 3 =>
  reify_change_dexpr_locals; shelve : expr_compiler.

(* Adding explicit patterns speeds up expr compilation by a factor ~10.
   We need Hint Extern because we want to shelve to make partial progress. *)
Notation DPAT p := (DEXPR _ _ _ p) (only parsing).

#[export] Hint Extern 5 (DPAT (word.add _ _)) =>
  simple eapply expr_compile_word_add; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (word.sub _ _)) =>
  simple eapply expr_compile_word_sub; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (word.mul _ _)) =>
  simple eapply expr_compile_word_mul; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (word.mulhuu _ _)) =>
  simple eapply expr_compile_word_mulhuu; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (word.divu _ _)) =>
  simple eapply expr_compile_word_divu; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (word.modu _ _)) =>
  simple eapply expr_compile_word_modu; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (word.and _ _)) =>
  simple eapply expr_compile_word_and; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (word.or _ _)) =>
  simple eapply expr_compile_word_or; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (word.xor _ _)) =>
  simple eapply expr_compile_word_xor; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (word.sru _ _)) =>
  simple eapply expr_compile_word_sru; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (word.slu _ _)) =>
  simple eapply expr_compile_word_slu; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (word.srs _ _)) =>
  simple eapply expr_compile_word_srs; shelve : expr_compiler.

#[export] Hint Extern 5 (DPAT (of_bool (word.lts _ _))) =>
  simple eapply expr_compile_word_lts; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_bool (word.ltu _ _))) =>
  simple eapply expr_compile_word_ltu; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_bool (word.eqb _ _))) =>
  simple eapply expr_compile_word_eqb; shelve : expr_compiler.

#[export] Hint Extern 5 (DPAT (of_Z (Z.add _ _))) =>
  simple eapply expr_compile_Z_add; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_Z (Z.sub _ _))) =>
  simple eapply expr_compile_Z_sub; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_Z (Z.mul _ _))) =>
  simple eapply expr_compile_Z_mul; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_Z (Z.land _ _))) =>
  simple eapply expr_compile_Z_land; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_Z (Z.lor _ _))) =>
  simple eapply expr_compile_Z_lor; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_Z (Z.lxor _ _))) =>
  simple eapply expr_compile_Z_lxor; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_Z (Z.shiftl _ _))) =>
  simple eapply expr_compile_Z_shiftl; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_Z (Z.shiftr _ _))) =>
  simple eapply expr_compile_Z_shiftr; shelve : expr_compiler.

#[export] Hint Extern 5 (DPAT (of_N (N.add _ _))) =>
  simple eapply expr_compile_N_add; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_N (N.sub _ _))) =>
  simple eapply expr_compile_N_sub; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_N (N.mul _ _))) =>
  simple eapply expr_compile_N_mul; shelve : expr_compiler.

#[export] Hint Extern 5 (DPAT (of_nat (Nat.add _ _))) =>
  simple eapply expr_compile_nat_add; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_nat (Nat.sub _ _))) =>
  simple eapply expr_compile_nat_sub; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_nat (Nat.mul _ _))) =>
  simple eapply expr_compile_nat_mul; shelve : expr_compiler.

#[export] Hint Extern 5 (DPAT (of_byte (byte.and _ _))) =>
  simple eapply expr_compile_byte_and; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_byte (byte.xor _ _))) =>
  simple eapply expr_compile_byte_xor; shelve : expr_compiler.

#[export] Hint Extern 5 (DPAT (of_bool (andb _ _))) =>
  simple eapply expr_compile_bool_andb; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_bool (orb _ _))) =>
  simple eapply expr_compile_bool_orb; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_bool (xorb _ _))) =>
  simple eapply expr_compile_bool_xorb; shelve : expr_compiler.

#[export] Hint Extern 6 (DEXPR _ _ _ (of_Z _)) =>
  simple eapply expr_compile_Z_literal; shelve : expr_compiler.
#[export] Hint Extern 6 (DEXPR _ _ _ _) =>
  simple eapply expr_compile_word_literal; shelve : expr_compiler.

Section Tests.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}.
  Context {mem: map.map word Byte.byte} {locals: map.map String.string word}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env: map.map string (list string * list string * cmd)}.

  Context (m: mem).

  Notation DEXPR l := (WeakestPrecondition.dexpr (mem := mem) (locals := locals) m l).

  Local Goal {e | forall w,
          DEXPR #{ "w" => w }# e (word.and (word.of_Z 3) w) }.
  Proof. eexists; intros; compile_expr. Qed.

  Local Goal {e | forall z,
          DEXPR #{ "z" => of_Z z }# e (word.of_Z (Z.land 3 z)) }.
  Proof. eexists; intros; compile_expr. Qed.

  Local Goal {e | forall b,
          DEXPR #{ "b" => of_byte b }# e (word_of_byte (byte.and Byte.x03 b)) }.
  Proof. eexists; intros; compile_expr. Qed.

  Local Goal {e | forall z n, (* Casts to Z come "for free" *)
          DEXPR #{ "z" => of_Z z; "n" => of_N n }# e (of_Z (Z.add z (Z.of_N n))) }.
  Proof. eexists; intros; compile_expr. Qed.

  Local Goal {e | forall b,
          DEXPR #{ "n" => word.b2w b }# e (word.b2w (andb b false)) }.
  Proof. eexists; intros; compile_expr. Qed.

  Local Goal {e | forall x b,
          DEXPR #{ "x" => word.of_Z x; "b" => word_of_byte b }# e
                (word.add (word.of_Z (Z.add x x))
                          (word_of_byte (byte.and b b))) }.
  Proof. eexists; intros; compile_expr. Qed.
End Tests.
