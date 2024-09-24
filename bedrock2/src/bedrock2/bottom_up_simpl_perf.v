From Coq Require Import ZArith. Local Open Scope Z_scope.
Require Import Ltac2.Ltac2. Set Default Proof Mode "Classic".
Require Import Ltac2.Printf.
Require Import coqutil.Tactics.foreach_hyp.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import bedrock2.bottom_up_simpl.
Require Import bedrock2.unzify.

Ltac2 filtered_bottom_up_simpl_in_hyp_of_type'(h: ident)(t: constr): unit :=
  if Ident.starts_with @__ h then ()
  else (printf "<infomsg>%I</infomsg>" h;
        Control.time None
          (fun _ => bottom_up_simpl_in_hyp_of_type silent_if_no_progress h t)).

Ltac2 filtered_bottom_up_simpl_in_hyp_of_type(h: ident)(t: constr): unit :=
  if Ident.starts_with @__ h then ()
  else bottom_up_simpl_in_hyp_of_type silent_if_no_progress h t.

Ltac2 simpl_in_hyps () := foreach_hyp filtered_bottom_up_simpl_in_hyp_of_type.

Ltac simpl_in_hyps := ltac2:(simpl_in_hyps ()).

Section Tests.

  Context {word: word.word 32} {word_ok: word.ok word}.
  Context {mem: Type}.
  Hypothesis bytearray : Z -> list Z -> word -> mem -> Prop.

  Add Ring wring : (Properties.word.ring_theory (word := word))
      ((* too expensive: preprocess [autorewrite with rew_word_morphism], *)
       morphism (Properties.word.ring_morph (word := word)),
       constants [Properties.word_cst]).

  Import ZList.List.ZIndexNotations. Local Open Scope zlist_scope.
  Import bedrock2.WordNotations. Local Open Scope word_scope.

  Goal forall (s1 s2 : list Z) (p1_pre p2_pre : word) (v : Z) (m0 m2 : mem)
              (p1' p2' c1 c2 p1 p2 : word),
      v = len s1 - \[p1' ^- p1_pre] ->
      bytearray (len s1 + 1) (s1 ++ [|0|]) p1_pre m0 ->
      bytearray (len s2 + 1) (s2 ++ [|0|]) p2_pre m2 ->
      \[p1' ^- p1_pre] <= len s1 ->
      \[p2' ^- p2_pre] <= len s2 ->
      \[p1' ^- p1_pre] = \[p2' ^- p2_pre] ->
      s1[:\[p1' ^- p1_pre]] = s2[:\[p2' ^- p2_pre]] ->
      c1 = /[(s1 ++ [|0|])[\[p1' ^- p1_pre]]] ->
      c2 = /[(s2 ++ [|0|])[\[p2' ^- p2_pre]]] ->
      p1 = p1' ^+ /[1] ->
      p2 = p2' ^+ /[1] ->
      c1 = c2 ->
      c1 <> /[0] ->
      \[p1' ^- p1_pre] <> len s1 ->
      \[p2' ^- p2_pre] = len s2 ->
      False.
  Proof.
    intros.
    zify_hyps.
    Time simpl_in_hyps. (* 0.748 secs *)
    (* Time bottom_up_simpl_in_hyps. 3.653 secs because it also simplifies __Z hyps *)
    unzify.
  Abort.
End Tests.
