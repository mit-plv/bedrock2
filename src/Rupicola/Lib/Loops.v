Require Import Arith PeanoNat.
Require Import Coq.Program.Wf.
Require Import Psatz.

Require Import Rupicola.Lib.Api.

Definition nlet {A P} (vars: list string) (val : A) (body : forall a : A, P a) : P val :=
  let x := val in body x.

(* Set Primitive Projections. *)
Record p2 {A B} := P2 { pfst: A; psnd: B }.
(* Unset Primitive Projections. *)
Arguments P2 {A B} pfst psnd: assert.
Arguments p2: clear implicits.

Lemma extends_refl {p o} {map: map.map p o} m:
  map.extends m m.
Proof. firstorder. Qed.

Lemma extends_eq {p o} {map: map.map p o} m1 m2:
  m1 = m2 ->
  map.extends m1 m2.
Proof. intros * ->; apply extends_refl. Qed.

(* FIXME Error: Anomaly "Uncaught exception Failure("hd")." until 8.13 *)
(* Notation "'let/n' x := val 'in' body" := *)
(*   (nlet [_] val (fun x => body)) *)
(*     (at level 200, x ident, body at level 200, *)
(*      format "'let/n'  x  :=  val  'in' '//' body", *)
(*      only printing). *)

Notation "'let/n' x 'as' nm := val 'in' body" :=
  (nlet (P := fun _ => _) (* Force non-dependent type *)
        [nm] val (fun x => body))
    (at level 200, x ident, body at level 200,
     format "'let/n'  x  'as'  nm  :=  val  'in' '//' body").

Notation "'let/n' x := val 'in' body" :=
  (nlet (P := fun _ => _) (* Force non-dependent type *)
        [IdentParsing.binder_to_string val x]
        val (fun x => body))
    (at level 200, x ident, body at level 200,
     only parsing).

(* Notation "'let/n' ( x , y ) := val 'in' body" := *)
(*   (nlet [_; _] val (fun '(x, y) => body)) *)
(*     (at level 200, x ident, body at level 200, *)
(*      format "'let/n'  ( x ,  y )  :=  val  'in' '//' body", *)
(*      only printing). *)

Notation "'let/n' ( x , y ) 'as' ( nx , ny ) := val 'in' body" :=
  (nlet (P := fun _ => _) (* Force non-dependent type *)
        [nx; ny] val (fun '(P2 x y) => body))
    (at level 200, x ident, body at level 200,
     format "'let/n'  ( x ,  y )  'as'  ( nx ,  ny )  :=  val  'in' '//' body").

Notation "'let/n' ( x , y ) := val 'in' body" :=
  (nlet (P := fun _ => _) (* Force non-dependent type *)
        [IdentParsing.binder_to_string (pfst val) x;
         IdentParsing.binder_to_string (psnd val) y]
        val (fun '(P2 x y) => body))
    (at level 200, x ident, y ident, body at level 200,
     only parsing).

Module Type ExitToken_sig.
  Axiom t : Set.
  Axiom new : bool -> t.
  Axiom get : t -> bool.
  Axiom set : t -> t.
End ExitToken_sig.

Module ExitToken <: ExitToken_sig.
  Definition t := bool.
  Definition new (b: bool) : t := b.
  Definition get (tok: t) : bool := tok.
  Definition set (tok: t) : t := true.
End ExitToken.

Class HasDefault (T: Type) := t: T.
Class Convertible (T1 T2: Type) := to_nat: T1 -> T2.

Fixpoint replace_nth {A} (n: nat) (l: list A) (a: A) {struct l} :=
  match l, n with
  | [], _ => []
  | _ :: t, 0 => a :: t
  | h :: t, S n => h :: replace_nth n t a
  end.

Lemma replace_nth_length {A} n (l: list A) a:
  List.length (replace_nth n l a) = List.length l.
Proof.
  revert n; induction l; cbn; intros.
  - reflexivity.
  - destruct n; simpl; rewrite ?IHl; reflexivity.
Qed.

Module FlatArray.
  Section FlatArray.
    Context {K V: Type}.
    Context {v0: HasDefault V}.
    Context {k2n: Convertible K nat}.

    Definition t := list V.
    Definition get (a: t) (k: K) : V := nth_default v0 a (k2n k).
    Definition put (a: t) (k: K) (v: V) : t := replace_nth (k2n k) a v.
    (* FIXME needs a compilation rule for get_default which generates a test *)
  End FlatArray.
End FlatArray.

Section Gallina.
  (* FIXME it's an interesting challenge here to decide what API “continue” should have. *)
  Program Fixpoint ranged_for {A}
          (from to step: nat)
          (body: forall (tok: ExitToken.t) (idx: nat) (acc: A), (ExitToken.t * A))
          (a0: A) {measure (to - from)} : A :=
    if le_gt_dec to from then a0
    else let (tok, a0) := body (ExitToken.new true) from a0 in
         if ExitToken.get tok then
           ranged_for (from + S (pred step)) to step body a0
         else a0.
  Next Obligation.
    lia.
  Defined.
End Gallina.

Section Compile.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.

  Definition ranged_for_w {A}
             (from to step: word)
             (body: forall (tok: ExitToken.t) (idx: word) (acc: A), (ExitToken.t * A))
             (a0: A) : A :=
    ranged_for (Z.to_nat (word.unsigned from))
               (Z.to_nat (word.unsigned to))
               (Z.to_nat (word.unsigned step))
               (fun tok idx v =>
                  body tok (word.of_Z (Z.of_nat idx)) v)
               a0.

  (* Set Primitive Projections. *)
  (* Record wp_args := *)
  (*   { Trace: Semantics.trace; *)
  (*     Memory: Semantics.mem; *)
  (*     Locals: Semantics.locals; *)
  (*     Functions: list (String.string * (list String.string * list String.string * cmd.cmd)) }. *)

  (* Definition wp_cmd body spec args := *)
  (*   (WeakestPrecondition.cmd *)
  (*      (WeakestPrecondition.call args.(Functions)) *)
  (*      body *)
  (*      (args.(Trace)) *)
  (*      (args.(Memory)) *)
  (*      (args.(Locals)) *)
  (*      spec). *)

  Notation "<{ 'Trace' := tr ; 'Memory' := mem ; 'Locals' := locals ; 'Functions' := functions }> cmd <{ post }>" :=
    (WeakestPrecondition.cmd
      (WeakestPrecondition.call functions)
      cmd tr mem locals post)
      (at level 0,
       format "'[v' <{  '[v' 'Trace'  :=  '[hv' tr ']' ;
                        '//' 'Memory'  :=  '[hv' mem ']' ;
                        '//' 'Locals'  :=  '[hv' locals ']' ;
                        '//' 'Functions'  :=  '[hv' functions ']' ']'  }>
               '//' cmd
               '//' <{  '[hv' post ']'  }> ']'").

  (* Programmer (or tactic script) should put bounds in locals before looping *)

  Definition predicate :=
    Semantics.trace -> Semantics.mem -> Semantics.locals -> Prop.

  Require Import Cells.Cells.

  Definition incr_gallina_spec (c: cell) : cell :=
      let/n one := word.of_Z 1 in
      let/n from := word.of_Z 3 in
      let/n to := word.of_Z 5 in
      let/n step := word.of_Z 1 in
      let/n tick := word.of_Z 0 in
      let/n (tick, c) :=
         ranged_for_w (A := p2 word cell)
                      from to step
                      (fun tok idx '(P2 tick c) =>
                         let/n v := get c in
                         let/n v := word.add v idx in
                         let/n c := put v c in
                         let/n tick := word.add tick one in
                         let/n from := to in
                         (tok, (P2 tick c)))
                      (P2 tick c) : p2 word cell in
      (let/n v := get c in
       let/n v := word.add v tick in
       let/n c := put v c in
       c).

  Print incr_gallina_spec.

  Local Infix "~>" := cell_value.

  (* FIXME find the way to preserve the name of the binder in ‘k’ instead of renaming everything to ‘head’ *)

  Lemma compile_constant :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr functions T (pred: T -> predicate) z k k_impl,
    forall var,
      let v := word.of_Z z in
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var v;
          Functions := functions }>
       k_impl
       <{ pred (k v) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.literal z)) k_impl
      <{ pred (nlet [var] v k) }>.
  Proof.
    intros.
    repeat straightline.
    eassumption.
  Qed.

  Lemma compile_read_local :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr functions T (pred: T -> predicate) v0 k k_impl
      src_var dst_var,
      map.get locals src_var = Some v0 ->
      let v := v0 in
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals dst_var v0;
          Functions := functions }>
       k_impl
       <{ pred (k v) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set dst_var (expr.var src_var)) k_impl
      <{ pred (nlet [dst_var] v k) }>.
  Proof.
    intros.
    repeat straightline.
    exists v0; split.
    - repeat red; eauto.
    - eauto.
  Qed.

  Lemma compile_get :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr R functions
      T (pred: T -> predicate)
      c c_ptr c_var k k_impl var,

      sep (cell_value c_ptr c) R mem ->
      map.get locals c_var = Some c_ptr ->

      let v := (get c) in
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var v;
          Functions := functions }>
       k_impl
       <{ pred (k v) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.load access_size.word (expr.var c_var)))
              k_impl
      <{ pred (nlet [var] v k) }>.
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

  Lemma compile_put :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr R functions
      T (pred: T -> predicate)
      c c_ptr c_var x x_var k k_impl,
      sep (cell_value c_ptr c) R mem ->
      map.get locals c_var = Some c_ptr ->
      map.get locals x_var = Some x ->
      let v := (put x c) in
      (let v := v in
       forall m,
         sep (cell_value c_ptr v) R m ->
         (<{ Trace := tr;
             Memory := m;
             Locals := locals;
             Functions := functions }>
          k_impl
          <{ pred (k v) }>)) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.store access_size.word (expr.var c_var) (expr.var x_var))
              k_impl
      <{ pred (nlet [c_var] v k) }>.
  Proof.
    intros.
    unfold cell_value in *.
    repeat straightline.
    exists c_ptr.
    split.
    { repeat straightline; eauto. }
    { eexists; split.
      { repeat straightline; eauto. }
      repeat straightline.
      subst v; simpl.
      match goal with
      | [ H: context[WeakestPrecondition.cmd] |- _ ] => apply H
      end.
      eassumption. }
  Qed.

  Arguments FlatArray.t V : clear implicits.

  Definition word_array_value (addr: address) (a: FlatArray.t word) : Semantics.mem -> Prop :=
    array scalar (word.of_Z (Memory.bytes_per_word Semantics.width)) addr a.

  Instance Convertible_word_Nat : Convertible word nat :=
    fun w => Z.to_nat (word.unsigned w).
  Instance HasDefault_word : HasDefault word :=
    word.of_Z 0.

  Lemma compile_wordarray_get :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr R functions
      T (pred: T -> predicate)
      a a_ptr a_var idx idx_var k k_impl var,

      sep (word_array_value a_ptr a) R mem ->
      map.get locals a_var = Some a_ptr ->
      map.get locals idx_var = Some idx ->

      (word.unsigned idx < Z.of_nat (List.length a))%Z ->

      let v := (FlatArray.get a idx) in
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var v;
          Functions := functions }>
       k_impl
       <{ pred (k v) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (cmd.set
           var
           (expr.load
              access_size.word
              (expr.op bopname.add
                       (expr.var a_var)
                       (expr.op bopname.mul
                                (expr.literal (Memory.bytes_per_word Semantics.width))
                                (expr.var idx_var)))))
        k_impl
      <{ pred (nlet [var] v k) }>.
  Proof.
    unfold word_array_value; cbn; intros.
    pose proof word.unsigned_range idx.
    exists (FlatArray.get a idx); split; cbn; [ | assumption ].
    exists a_ptr; split; [ eassumption | ]; cbn.
    exists idx; split; [ eassumption | ]; cbn.
    eexists; split; [ | reflexivity ].

    eapply load_word_of_sep.
    seprewrite_in open_constr:(array_index_nat_inbounds
                                 _ _ _ _ (Z.to_nat (word.unsigned idx))) H;
      [ lia | ].

    repeat rewrite ?word.ring_morph_mul, ?word.of_Z_unsigned, ?Z2Nat.id in H6 by lia.
    unfold FlatArray.get, Convertible_word_Nat, HasDefault_word, HasDefault.
    rewrite List.hd_skipn_nth_default.
    ecancel_assumption.
  Qed.

  Lemma compile_wordarray_put :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr R functions
      T (pred: T -> predicate)
      a a_ptr a_var idx idx_var val val_var k k_impl var,

      sep (word_array_value a_ptr a) R mem ->
      map.get locals a_var = Some a_ptr ->
      map.get locals idx_var = Some idx ->
      map.get locals val_var = Some val ->

      (word.unsigned idx < Z.of_nat (List.length a))%Z ->

      let a := (FlatArray.put a idx val) in
      (let a := a in
       forall mem',
         sep (word_array_value a_ptr a) R mem' ->
         <{ Trace := tr;
            Memory := mem';
            Locals := locals;
            Functions := functions }>
         k_impl
         <{ pred (k a) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (cmd.store
           access_size.word
           (expr.op bopname.add
                    (expr.var a_var)
                    (expr.op bopname.mul
                             (expr.literal (Memory.bytes_per_word Semantics.width))
                             (expr.var idx_var)))
           (expr.var val_var))
        k_impl
      <{ pred (nlet [var] a k) }>.
  Proof.
    unfold word_array_value; cbn; intros.
    pose proof word.unsigned_range idx.
    eexists; split; cbn.

    {
    eexists; split; [ eassumption | ]; cbn.
    eexists; split; [ eassumption | reflexivity ].
    }

    { eexists; split; cbn.
      { eexists; split; [ eassumption | reflexivity ]. }
      { red.
        seprewrite_in           (* FIXME: BEDROCK2: Adding an extra "_" at the end shelves an inequality *)
          open_constr:(array_index_nat_inbounds
                         _ _ _ _ (Z.to_nat (word.unsigned idx))) H;
          [ lia | ].
        instantiate (1 := HasDefault_word) in H7.
        eapply store_word_of_sep.
        { repeat rewrite ?word.ring_morph_mul, ?word.of_Z_unsigned, ?Z2Nat.id in H7 by lia.
          ecancel_assumption. }
        { intros m Hm.
          apply H4.
          unfold FlatArray.put, Convertible_word_Nat, HasDefault_word, HasDefault.
          seprewrite open_constr:(array_index_nat_inbounds (* FIXME: BEDROCK2: Sequencing a failing tactic after a seprewrite backtracks into seprewrite itself; intended? *)
                                    _ _ _ _ (Z.to_nat (word.unsigned idx)));
            [ rewrite replace_nth_length; lia | ].
          instantiate (1 := HasDefault_word).
          repeat rewrite ?word.ring_morph_mul, ?word.of_Z_unsigned, ?Z2Nat.id by lia.
          replace (List.firstn (Z.to_nat (word.unsigned idx))
                               (replace_nth (Z.to_nat (word.unsigned idx)) a val))
            with (List.firstn (Z.to_nat (word.unsigned idx)) a) by admit.
          replace (List.skipn (S (Z.to_nat (word.unsigned idx)))
                              (replace_nth (Z.to_nat (word.unsigned idx)) a val)) with
              (List.skipn (S (Z.to_nat (word.unsigned idx))) a) by admit.
          replace (List.hd _ (* FIXME: COQ: replace should allow patterns like change *)
                           (List.skipn (Z.to_nat (word.unsigned idx))
                                       (replace_nth (Z.to_nat (word.unsigned idx)) a val))) with
              val by admit.
          ecancel_assumption. }
  Admitted.

  Lemma compile_skip :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr functions (pred: predicate),
      pred tr mem locals  ->
      (<{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       cmd.skip
       <{ pred }>).
  Proof.
    intros.
    repeat straightline.
    assumption.
  Qed.

  (* FIXME check out what happens when running straightline on a triple with a cmd.seq; could we get rid of the continuation arguments?  Would it require more rewrites? *)
  Lemma compile_unset :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr functions (pred: predicate)
      var cmd,
      <{ Trace := tr;
         Memory := mem;
         Locals := map.remove locals var;
         Functions := functions }>
      cmd
      <{ pred }> ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.unset var) cmd
      <{ pred }>.
  Proof.
    repeat straightline'. eauto.
  Qed.

  Lemma compile_unsets :
    forall vars (locals: Semantics.locals) (mem: Semantics.mem)
      cmd tr functions (pred: predicate),
      (<{ Trace := tr;
          Memory := mem;
          Locals := List.fold_left map.remove vars locals;
          Functions := functions }>
       cmd
       <{ pred }>) ->
      (<{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       fold_right (fun v c => cmd.seq (cmd.unset v) c) cmd vars
       <{ pred }>).
  Proof.
    induction vars; cbn [fold_right]; intros.
    - assumption.
    - apply compile_unset.
      apply IHvars.
      assumption.
  Qed.

  Lemma compile_add :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr functions T (pred: T -> predicate)
      x x_var y y_var k k_impl var,
      map.get locals x_var = Some x ->
      map.get locals y_var = Some y ->
      let v := word.add x y in
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var v;
          Functions := functions }>
       k_impl
       <{ pred (k v) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.op bopname.add (expr.var x_var) (expr.var y_var)))
              k_impl
      <{ pred (nlet [var] v k) }>.
  Proof.
    intros.
    repeat straightline.
    eexists; split.
    { repeat straightline.
        exists x; split; try eassumption.
        repeat straightline.
        exists y; split; try eassumption.
        reflexivity. }
    red.
    eassumption.
  Qed.

  (* Lemma compile_ranged_for : *)
  (*   forall (locals: Semantics.locals) (mem: Semantics.mem) *)
  (*     A T *)
  (*     (loop_pred: nat -> (bool * A) -> predicate) *)
  (*     (k_pred: T -> predicate) *)
  (*     tr functions *)
  (*     vars *)
  (*     (from to step: nat) *)
  (*     (from_var to_var step_var: string) *)
  (*     body body_impl *)
  (*     k k_impl *)
  (*     (a0: A), *)
  (*     loop_pred from (true, a0) tr mem locals -> *)
  (*     (* fixme make a shorter alias for this *) *)
  (*     option_map word.unsigned (map.get locals from_var) = Some (Z.of_nat from) -> *)
  (*     option_map word.unsigned (map.get locals to_var) = Some (Z.of_nat to) -> *)
  (*     option_map word.unsigned (map.get locals step_var) = Some (Z.of_nat step) -> *)
  (*     let v := ranged_for from to step body a0 in *)
  (*     ((* loop body *) *)
  (*      forall tr mem locals from', *)
  (*        let a := ranged_for from from' step body a0 in *)
  (*        loop_pred from' (true, a) tr mem locals -> *)
  (*        (<{ Trace := tr; *)
  (*            Memory := mem; *)
  (*            Locals := locals; *)
  (*            Functions := functions }> *)
  (*         body_impl *)
  (*         <{ loop_pred from' (body from' a) }>)) -> *)
  (*     (let v := v in *)
  (*      forall tr mem locals, *)
  (*        loop_pred to (false, v) tr mem locals -> *)
  (*        (<{ Trace := tr; *)
  (*            Memory := mem; *)
  (*            Locals := locals; *)
  (*            Functions := functions }> *)
  (*         k_impl *)
  (*         <{ k_pred (k v) }>)) -> *)
  (*     (let v := v in *)
  (*      <{ Trace := tr; *)
  (*         Memory := mem; *)
  (*         Locals := locals; *)
  (*         Functions := functions }> *)
  (*      cmd.seq *)
  (*        (cmd.while *)
  (*           (expr.op bopname.ltu (expr.var from_var) (expr.var to_var)) *)
  (*           (cmd.seq *)
  (*              (cmd.set from_var *)
  (*                       (expr.op bopname.add *)
  (*                                (expr.var from_var) *)
  (*                                (expr.literal 1))) *)
  (*              body_impl)) *)
  (*        k_impl *)
  (*      <{ k_pred (nlet vars v k) }>). *)
  (* Proof. *)
  (*   cbv zeta. *)
  (*   repeat straightline'. *)
  (* Admitted. *)

  Lemma compile_ranged_for_w {A T}:
    forall tr mem locals functions
      (loop_pred: word -> A -> predicate)
      (k_pred: T -> predicate)
      (from to step: word)
      (from_var to_var step_var: string)
      (a0: A) vars
      body body_impl
      k k_impl,
      let lp from '(tok, acc) tr mem locals :=
          loop_pred (if ExitToken.get tok then from else to) acc tr mem locals in
      (forall from a0 tr mem locals,
          loop_pred from a0 tr mem locals ->
          map.getmany_of_list locals [from_var; to_var; step_var] =
          Some [from; to; step]) ->
      loop_pred from a0 tr mem locals ->
      let v := ranged_for_w from to step body a0 in
      ((* loop body *)
        let lp := lp in
        forall tr mem locals from',
          let tok := ExitToken.new true in
          let a := ranged_for_w from from' step body a0 in
          (word.unsigned from <= word.unsigned from')%Z ->
          (word.unsigned from' < word.unsigned to)%Z ->
          loop_pred from' a tr mem locals ->
          (<{ Trace := tr;
              Memory := mem;
              Locals := locals;
              Functions := functions }>
           body_impl
           <{ lp from' (body tok from' a) }>)) ->
      (let v := v in
       forall tr mem locals,
         loop_pred to v tr mem locals ->
         (<{ Trace := tr;
             Memory := mem;
             Locals := locals;
             Functions := functions }>
          k_impl
          <{ k_pred (k v) }>)) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (cmd.while
           (expr.op bopname.ltu (expr.var from_var) (expr.var to_var))
           (cmd.seq
              (cmd.set from_var
                       (expr.op bopname.add
                                (expr.var from_var)
                                (expr.literal 1)))
              body_impl))
        k_impl
      <{ k_pred (nlet vars v k) }>.
  Proof.
    cbv zeta.
    repeat straightline'.
  Admitted.

  Instance spec_of_incr : spec_of "incr" :=
    (forall! (c_ptr : address) (c :cell),
        (sep (c_ptr ~> c))
          ===>
          "incr" @ [c_ptr]
          ===>
          (OneCell c_ptr (incr_gallina_spec c))).

  Lemma postcondition_func_norets_postcondition_cmd
        {T} spec (x: T) cmd R tr mem locals functions :
    (let pred :=
         (fun a (t : Semantics.trace) (m : Semantics.mem) (_ : Semantics.locals) =>
            postcondition_func_norets (spec a) R tr t m []) in
     WeakestPrecondition.cmd
       (WeakestPrecondition.call functions)
      cmd tr mem locals (pred x)) ->
    WeakestPrecondition.cmd
      (WeakestPrecondition.call functions)
      cmd tr mem locals
      (fun tr' m' locals' =>
         postcondition_func_norets (spec x) R tr tr' m' []).
  Proof. intros H; apply H. Qed.

  (* Lemma postcondition_func_postcondition_cmd *)
  (*       {T} spec (x: T) cmd R tr mem locals functions retvars : *)
  (*   (WeakestPrecondition.cmd *)
  (*      (WeakestPrecondition.call functions) *)
  (*      cmd tr mem locals *)
  (*      (postcondition_cmd *)
  (*         (fun _ => True) spec retvars R tr)) -> *)
  (*   WeakestPrecondition.cmd *)
  (*     (WeakestPrecondition.call functions) *)
  (*     cmd tr mem locals *)
  (*     (fun tr' m' locals' => *)
  (*        WeakestPrecondition.list_map *)
  (*          (WeakestPrecondition.get locals') retvars *)
  (*          (fun rets : list word => *)
  (*             postcondition_func spec R tr tr' m' rets)). *)
  (* Proof. *)
  (*   cbv [postcondition_func postcondition_cmd]; intros. *)
  (*   cleanup. *)
  (*   use_hyp_with_matching_cmd; cleanup; subst. *)
  (*   eapply getmany_list_map; sepsimpl; eauto. *)
  (* Qed. *)

  Ltac solve_map_get_goal ::=
    repeat lazymatch goal with
           | [ H: map.extends ?m2 ?m1 |- map.get ?m2 ?k = Some ?v ] =>
             apply (fun p => @map.extends_get _ _ _ m1 m2 k v p H)
           | [  |- map.get ?m _ = Some ?val ] =>
             first [ apply map.get_put_same | rewrite map.get_put_diff ]
           | [  |- map.get ?m _ = None ] =>
             first [ apply map.get_empty | rewrite map.get_put_diff by congruence ]
           | [  |- _ <> _ ] => congruence
           end.

  Ltac compile_get_binding :=
    lazymatch goal with
    | |- context [ WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet _ ?v _)) ] => v
    end.

   Ltac compile_custom ::=
     (* simple apply ensures that Coq doesn't unfold [nlet]s *)
     first [let v := compile_get_binding in
            is_var v; simple apply compile_read_local |
            simple apply compile_constant |
            simple eapply compile_add |
            simple eapply compile_get |
            simple eapply compile_put |
            simple eapply compile_wordarray_get |
            simple eapply compile_wordarray_put ].

   Ltac compile_setup :=
     cbv [program_logic_goal_for];
     (* modified version of a clause in straightline *)
     (intros; WeakestPrecondition.unfold1_call_goal;
      (cbv beta match delta [WeakestPrecondition.call_body]);
      lazymatch goal with
      | |- if ?test then ?T else _ =>
        replace test with true by reflexivity; change_no_check T
      end; cbv beta match delta [WeakestPrecondition.func]);
     repeat straightline; subst_lets_in_goal; cbn [length];
     first [ apply postcondition_func_norets_postcondition_cmd
           (* | apply postcondition_func_postcondition_cmd *) ];
     intros;
     lazymatch goal with
     | |- context [ WeakestPrecondition.cmd _ _ _ _ _ (?pred ?spec) ] =>
       let hd := term_head spec in
       unfold hd
     | |- context [ postcondition_cmd _ (fun r => ?pred ?spec r) ] => (* FIXME *)
       let hd := term_head spec in
       unfold hd
     | _ => fail "Postcondition not in expected shape (?pred gallina_spec)"
     end.

   Notation "∅" := map.empty.
   Notation "m [[ k ← v ]]" :=
     (map.put m k v)
       (left associativity, at level 11,
        format "m [[ k  ←  v ]]").

   Ltac try_unify x y :=
     try ((unify x y; fail 1) || fail 1 "Does not unify").

   Ltac lookup_variable m val ::=
     match m with
     | map.put _ ?k ?val' =>
       let t := type of val in
       let _ := constr:(@eq_refl t val <: val = val') in
       constr:(k)
     | map.put ?m' _ _ => lookup_variable m' val
     | _ => fail "lookup_variable: no results found"
     end.

   Ltac cleanup_hyp H :=
     lazymatch type of H with
     | ?x = _ =>
       tryif is_var x then subst x else idtac
     | match ?x with _ => _ end =>
       destruct x eqn:?; cleanup_hyp H
     | _ /\ _ =>
       let Hl := fresh "Hl" in
       let Hr := fresh "Hr" in
       destruct H as (Hl & Hr);
       cleanup_hyp Hl; cleanup_hyp Hr
     | _ => idtac
     end.

   Class A := a : nat.
   Fail Definition example := a.
   (* Weird quotes: ?A : "A" *)
   (* Error: Unable to satisfy the following constraints:
UNDEFINED EVARS:
 ?X101685==[semantics semantics_ok len a1 a2 |- Interface.word ?width] (parameter word of
             @word.of_Z) {?word}
 ?X101688==[semantics semantics_ok len a1 a2 (zero:=word.of_Z 0) |-
             HasDefault word] (parameter v0 of @FlatArray.get) {?v0}
 ?X101689==[semantics semantics_ok len a1 a2 (zero:=word.of_Z 0) |-
             Convertible ?word nat] (parameter k2n of @FlatArray.get) {?k2n}
 ?X101692==[semantics semantics_ok len a1 a2 (zero:=word.of_Z 0) (v:=
             FlatArray.get a1 zero) |- Convertible ?word nat] (parameter k2n of
             @FlatArray.put) {?k2n0}
TYPECLASSES:?X101685 ?X101688 ?X101689 ?X101692
 *)

   (* FIXME Loop lemma should maybe copy from, to, step into temporaries? *)
   Definition memcpy (len: word) (a1 a2: FlatArray.t word) :=
     let/n from := word.of_Z 0 in
     let/n step := word.of_Z 1 in
     let/n a2 := ranged_for_w
                  from len step
                  (fun tok idx a2 =>
                     let/n v := FlatArray.get a1 idx in
                     let/n a2 := FlatArray.put a2 idx v in
                     (tok, a2)) a2 in
     (a1, a2).

   Definition TwoByteArrays a1_ptr a2_ptr :=
     (fun '(a1, a2) (_retvals: list word) =>
        (word_array_value a1_ptr a1 * word_array_value a2_ptr a2)%sep).

   Locate "forall!".
   Instance spec_of_memcpy : spec_of "memcpy" :=
     (forall! (len: word) (a1_ptr a2_ptr : address) (a1 a2: FlatArray.t word),
         (fun R mem =>
            (word.unsigned len < Z.of_nat (List.length a1))%Z /\
            (word.unsigned len < Z.of_nat (List.length a2))%Z /\
            sep (word_array_value a1_ptr a1 * word_array_value a2_ptr a2)%sep R mem)
         ===>
         "memcpy" @ [len; a1_ptr; a2_ptr]
         ===>
         (TwoByteArrays a1_ptr a2_ptr (memcpy len a1 a2))).

   Require Import AdmitAxiom.
   Derive body SuchThat
         (let memcpy := ("memcpy", (["len"; "a1"; "a2"], [], body)) in
          program_logic_goal_for
            memcpy
            (ltac:(let x := program_logic_goal_for_function
                              memcpy (@nil string) in
                   exact x)))
         As body_correct.
   Proof.
     match goal with
     | [  |- context[?spec] ] =>
       match type of spec with
       | spec_of _ => cbv [spec]
       end
     end.

     compile_setup.

     repeat compile_step.

     eapply compile_ranged_for_w with (loop_pred := (fun idx a2 tr' mem' locals' =>
         tr' = tr /\
         locals' = (∅[["len" ← len]][["a1" ← a1_ptr]][["a2" ← a2_ptr]]
                     [["from" ← idx]][["step" ← v0]]) /\
         (word_array_value a1_ptr a1 * word_array_value a2_ptr a2 * R)%sep mem')).

     { intros * Hpred. cleanup_hyp Hpred.
       repeat apply map.getmany_of_list_cons; compile_step. }

     { eauto. }

     { intros * Hle Hlt Hpred. cleanup_hyp Hpred.

       repeat compile_step.

       { lia. }
       { admit. (* FIXME: There is something smart here: we need to check that the index is in bounds but we modified the array.  Using a vector type instead would keep the information in the type and the statement of Put would specify that the length is preserved.  Alternatively we could do an automatic induction? *)
       }

       { apply (compile_unsets ["v"]).
         apply compile_skip.

         red; repeat apply conj.
         + reflexivity.
         + cbn.
           repeat first [rewrite map.remove_put_diff by congruence |
                         rewrite map.remove_put_same by congruence |
                         rewrite map.remove_empty ].
           reflexivity.
         + ecancel_assumption. } }

     { intros * Hpred. cleanup_hyp Hpred.
       repeat compile_step.

       apply compile_skip.
       do 3 red; repeat apply conj.
       + reflexivity.
       + apply sep_assoc; rewrite sep_emp_l; split.
         * reflexivity.
         * Hint Unfold TwoByteArrays : compiler.
           autounfold with compiler.
           ecancel_assumption. }
   Qed.

   Require Import AdmitAxiom.
   Derive body SuchThat
         (let incr := ("incr", (["c"], [], body)) in
          program_logic_goal_for
            incr
            (ltac:(let x := program_logic_goal_for_function
                              incr (@nil string) in
                   exact x)))
         As body_correct.
   Proof.
     cbv [spec_of_incr].
     compile_setup.

     repeat compile_step.

     (* FIXME should the variable set always be in the form “extends”?  Or should we add explicit unsets? *)
     eapply compile_ranged_for_w with (loop_pred := (fun idx acc tr' mem' locals' =>
         let '(P2 tick c) := acc in
         tr' = tr /\
         (* locals' = map.put locals "tick" tick /\ *)
         locals' = (∅[["c" ← c_ptr]][["one" ← v]]
                     [["from" ← idx]][["to" ← v1]][["step" ← v2]]
                     [["tick" ← tick]]) /\
         (c_ptr ~> c * R)%sep mem')).

     { intros * Hpred. cleanup_hyp Hpred.
       (* eapply map.getmany_of_list_extends; eauto. *)
       repeat apply map.getmany_of_list_cons; compile_step. }

     { eauto using eq_refl.
       (* + subst locals; rewrite map.put_put_same; reflexivity. *) }

     { intros * Hpred. red in Hpred; cleanup_hyp Hpred.

       repeat compile_step.

       (* FIXME 3 options:
          - use a predicate that says `map.extends locals ...`;
          - use a predicate that says `locals = …` and add calls to `unset` [Jade-approved]
          - add a [map.extends] and an existential in the post-condition of the compilation lemma, not in the predicate itself *)
       eapply compile_unsets.   (* Forget local bindings *)
       apply compile_skip.

       red; repeat apply conj.
       + reflexivity.
       + (* apply extends_eq. *)
         instantiate (1 := ["v"]).
         cbn.
         (* match goal with *)
         (* | [ H: map.extends locals ?m |- _ ] => replace locals with m by admit *)
         (* end. *)
         repeat first [rewrite map.remove_put_diff by congruence |
                       rewrite map.remove_put_same by congruence |
                       rewrite map.remove_empty ].
         admit.
       + eauto. }

     { intros * Hpred. red in Hpred; cleanup_hyp Hpred.
       change (if ExitToken.get (ExitToken.new true) then ?x else _) with x.
       repeat compile_step.

       apply compile_skip.
       do 3 red; repeat apply conj.
       + reflexivity.
       + apply sep_assoc; rewrite sep_emp_l; split.
         * reflexivity.
         * autounfold with compiler.
           ecancel_assumption. }
   Qed.

  (* Require Import bedrock2.NotationsCustomEntry. *)
  (* Require Import bedrock2.NotationsInConstr. *)
  (* Print body. *)
End with_semantics.
