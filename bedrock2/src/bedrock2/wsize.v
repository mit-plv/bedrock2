(* Implementation of mulhuu by Andres Erbsen. *)

Require Import bedrock2.NotationsCustomEntry.
Require Import coqutil.Macros.ident_to_string.
From bedrock2 Require Import WeakestPrecondition ProgramLogic.
Require Import bedrock2.ZnWords.
From Coq Require Import Lia ZArith.

Import bedrock2.Syntax.
From Coq Require Import BinInt String List Init.Byte. Import ListNotations.
Import coqutil.Word.Interface coqutil.Word.Properties.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section WithSemantics.
Context {width} {BW : Bitwidth.Bitwidth width} {word : word.word width} {word_ok : word.ok word}.
Context {locals : Interface.map.map string word}.
Context {mem : Interface.map.map word byte}.
Context {ext_spec : Semantics.ExtSpec}.

Definition wmask : expr.expr := bedrock_expr:((-$1>>$27)&$63).
Definition wsize : expr.expr := bedrock_expr:($wmask+$1).

Lemma eval_wmask' : (word.and (word.sru (word.opp (word.of_Z 1)) (word.of_Z 27)) (word.of_Z 63)) = word.of_Z (width-1) :> word.
Proof.
  case BW as [ [ -> | -> ] ];
  apply word.unsigned_inj;
    rewrite ?word.unsigned_and_nowrap, ?word.unsigned_sru_nowrap, ?word.unsigned_opp;
    rewrite ?word.unsigned_of_Z; cbv [word.wrap]; cbv; trivial.
Qed.

Lemma eval_wsize' : word.add (word.and (word.sru (word.opp (word.of_Z 1)) (word.of_Z 27)) (word.of_Z 63)) (word.of_Z 1) = word.of_Z width :> word.
Proof.
  case BW as [ [ -> | -> ] ];
  apply word.unsigned_inj;
    repeat rewrite ?word.unsigned_and_nowrap, ?word.unsigned_sru_nowrap, ?word.unsigned_opp, ?word.unsigned_add_nowrap;
    rewrite ?word.unsigned_of_Z; cbv [word.wrap]; cbv; trivial.
Qed.

Import Map.Interface. (* Coercions *)

Lemma eval_wmask (m : mem) (l : locals) : Semantics.eval_expr m l wmask = Some (word.of_Z (width-1)).
Proof. cbn. rewrite eval_wmask'; trivial. Qed.
Lemma eval_wsize (m : mem) (l : locals) : Semantics.eval_expr m l wsize = Some (word.of_Z width).
Proof. cbn. rewrite eval_wsize'; trivial. Qed.
End WithSemantics.
