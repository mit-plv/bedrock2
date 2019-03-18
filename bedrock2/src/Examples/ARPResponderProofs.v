From Coq Require Import Strings.String Lists.List ZArith.BinInt.
From bedrock2 Require Import BasicC64Semantics ProgramLogic.

Require Import bedrock2.Examples.ARPResponder.

Import ListNotations.
Local Open Scope string_scope. Local Open Scope list_scope. Local Open Scope Z_scope.
Require Import bedrock2.NotationsInConstr.
From coqutil.Word Require Import Interface.

From bedrock2 Require Import Array Scalars Separation.
From coqutil.Tactics Require Import letexists rdelta.
Local Notation bytes := (array scalar8 (word.of_Z 1)).

Lemma word__if_zero (t:bool) (H : word.unsigned (if t then word.of_Z 1 else word.of_Z 0) = 0) : t = false. Admitted.
Lemma word__if_nonzero (t:bool) (H : word.unsigned (if t then word.of_Z 1 else word.of_Z 0) <> 0) : t = true. Admitted.

Set Printing Width 90.
Ltac seplog_use_array_load1 H i :=
  let iNat := eval cbv in (Z.to_nat i) in
  unshelve SeparationLogic.seprewrite_in @array_index_nat_inbounds H;
    [exact iNat|exact (word.of_Z 0)|Lia.lia|];
  change ((word.unsigned (word.of_Z 1) * Z.of_nat iNat)%Z) with i in *.

Local Instance spec_of_arp : spec_of "arp" := fun functions =>
  forall t m packet ethbuf len R,
    (sep (array scalar8 (word.of_Z 1) ethbuf packet) R) m ->
    word.unsigned len = Z.of_nat (length packet) ->
  WeakestPrecondition.call functions "arp" t m [ethbuf; len] (fun T M rets => True).
Goal program_logic_goal_for_function! arp.
  repeat straightline.
  letexists; split; [solve[repeat straightline]|]; split; [|solve[repeat straightline]]; repeat straightline.
  eapply word__if_nonzero in H1.
  rewrite word.unsigned_ltu, word.unsigned_of_Z, Z.mod_small in H1 by admit.
  eapply Z.ltb_lt in H1.
  repeat (letexists || straightline).
  split.
  1: repeat (split || letexists || straightline).
  Ltac tload := 
  lazymatch goal with |- Memory.load Syntax.access_size.one ?m (word.add ?base (word.of_Z ?i)) = Some ?v =>
  lazymatch goal with H: _ m |- _ =>
    let iNat := eval cbv in (Z.to_nat i) in
    SeparationLogic.seprewrite_in @array_index_nat_inbounds H;
    [instantiate (1 := iNat); Lia.lia|instantiate (1 := word.of_Z 0) in H];
    eapply load_one_of_sep;
    simple refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ H); clear H;
    SeparationLogic.cancel;
    simple refine (SeparationLogic.cancel_seps_at_indices 1 0 _ _ _ _); cbn [id];
      eapply RelationClasses.reflexivity
  end end.
  all: try tload.
  1: { straightline. }
  split; [|solve[repeat straightline]]; repeat straightline.
  
  letexists; split.
  1: repeat (split || letexists || straightline).
  all: try tload.
  1: { straightline. }
  split; [|solve[repeat straightline]]; repeat straightline.

  lazymatch goal with |- WeakestPrecondition.store Syntax.access_size.one ?m ?a ?v ?post =>
  lazymatch goal with H: _ m |- _ =>
    cbv [WeakestPrecondition.store];
      eapply store_one_of_sep;
    let a := rdelta a in
    let i := lazymatch a with word.add ?base (word.of_Z ?i) => i end in
    let iNat := eval cbv in (Z.to_nat i) in
    SeparationLogic.seprewrite_in @array_index_nat_inbounds H;
    [instantiate (1 := iNat); Lia.lia|instantiate (1 := word.of_Z 0) in H]
  end end.
  1: {
    simple refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ H); clear H;
    SeparationLogic.cancel;
    simple refine (SeparationLogic.cancel_seps_at_indices 1 0 _ _ _ _); cbn [id];
      eapply RelationClasses.reflexivity. }

  (* FIXME: make SeparationLogic.ecancel not reduce list functions *)
  
 (*  ============================ *)
 (*  forall m0 : Interface.map.rep, *)
 (*  sep (scalar8 a (word.of_Z (word.unsigned v2))) *)
 (*    (fun m1 : Interface.map.rep => *)
 (*     exists mp mq : Interface.map.rep, *)
 (*       Interface.map.split m1 mp mq /\ *)
 (*       bytes ethbuf (firstn 21 packet) mp /\ *)
 (*       (fix seps (xs : list (Interface.map.rep -> Prop)) : Interface.map.rep -> Prop := *)
 (*          match xs with *)
 (*          | [] => emp True *)
 (*          | [x] => x *)
 (*          | x :: (_ :: _) as xs0 => sep x (seps xs0) *)
 (*          end) *)
 (*         ((fix app (l0 m2 : list (Interface.map.rep -> Prop)) {struct l0} : *)
 (*             list (Interface.map.rep -> Prop) := *)
 (*             match l0 with *)
 (*             | [] => m2 *)
 (*             | a0 :: l1 => a0 :: app l1 m2 *)
 (*             end) *)
 (*            ((fix firstn (n : nat) (l0 : list (Interface.map.rep -> Prop)) {struct n} : *)
 (*                list (Interface.map.rep -> Prop) := *)
 (*                match n with *)
 (*                | 0%nat => [] *)
 (*                | S n0 => match l0 with *)
 (*                          | [] => [] *)
 (*                          | a0 :: l1 => a0 :: firstn n0 l1 *)
 (*                          end *)
 (*                end) 0%nat *)
 (*               [scalar8 *)
 (*                  (word.add ethbuf *)
 (*                     (word.of_Z (word.unsigned (word.of_Z 1) * Z.of_nat 21))) *)
 (*                  (hd (word.of_Z 0) (skipn 21 packet)); *)
 (*               bytes *)
 (*                 (word.add *)
 (*                    (word.add ethbuf *)
 (*                       (word.of_Z (word.unsigned (word.of_Z 1) * Z.of_nat 21))) *)
 (*                    (word.of_Z 1)) (tl (skipn 21 packet)); R]) *)
 (*            (tl *)
 (*               (skipn 1 *)
 (*                  [bytes ethbuf (firstn 21 packet); *)
 (*                  scalar8 *)
 (*                    (word.add ethbuf *)
 (*                       (word.of_Z (word.unsigned (word.of_Z 1) * Z.of_nat 21))) *)
 (*                    (hd (word.of_Z 0) (skipn 21 packet)); *)
 (*                  bytes *)
 (*                    (word.add *)
 (*                       (word.add ethbuf *)
 (*                          (word.of_Z (word.unsigned (word.of_Z 1) * Z.of_nat 21))) *)
 (*                       (word.of_Z 1)) (tl (skipn 21 packet)); R]))) mq) m0 -> *)
 (*  WeakestPrecondition.cmd (WeakestPrecondition.call functions) c30 t m0 l *)
 (*    (fun (_ : Semantics.trace) (_ l0 : Interface.map.rep) => *)
 (*     WeakestPrecondition.list_map (WeakestPrecondition.get l0) [] *)
 (*       (fun _ : list Semantics.word => True)) *)
Abort.