(* Implementation of mulhuu by Andres Erbsen. *)

Require Import bedrock2.NotationsCustomEntry.
Require Import coqutil.Macros.ident_to_string.
From bedrock2 Require Import WeakestPrecondition ProgramLogic.
Require Import bedrock2.ZnWords.
From Coq Require Import Lia ZArith.

Import bedrock2.Syntax.
From Coq Require Import BinInt String List Init.Byte. Import ListNotations.
Import coqutil.Word.Bitwidth coqutil.Word.Properties.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section WithSemantics.
Context {width} {BW : Bitwidth.Bitwidth width}.
Local Notation word := (bits width).
Context {locals : Interface.map.map string word}.
Context {mem : Interface.map.map word byte}.
Context {ext_spec : Semantics.ExtSpec}.

Definition wmask : expr.expr := bedrock_expr:((-$1>>$27)&$63).
Definition wsize : expr.expr := bedrock_expr:($wmask+$1).

Lemma eval_wmask' : (Zmod.and (Zmod.sru (Zmod.opp (bits.of_Z width 1)) 27) (bits.of_Z width 63)) = bits.of_Z width (width-1) :> word.
Proof.
  case BW as [ [ -> | -> ] ]; apply Zmod.unsigned_inj; vm_compute; reflexivity.
Qed.

Lemma eval_wsize' : Zmod.add (Zmod.and (Zmod.sru (Zmod.opp (bits.of_Z width 1)) 27) (bits.of_Z width 63)) (bits.of_Z width 1) = bits.of_Z width width :> word.
Proof.
  case BW as [ [ -> | -> ] ]; apply Zmod.unsigned_inj; vm_compute; reflexivity.
Qed.

Import Map.Interface. (* Coercions *)

Lemma eval_wmask (m : mem) (l : locals) : Semantics.eval_expr m l wmask = Some (bits.of_Z width (width-1)).
Proof. cbn. unfold Semantics.sru. rewrite shamt_of_Z_small by (destruct width_cases as [-> | ->]; lia). rewrite eval_wmask'; trivial. Qed.
Lemma eval_wsize (m : mem) (l : locals) : Semantics.eval_expr m l wsize = Some (bits.of_Z width width).
Proof. cbn. unfold Semantics.sru. rewrite shamt_of_Z_small by (destruct width_cases as [-> | ->]; lia). rewrite eval_wsize'; trivial. Qed.
End WithSemantics.
