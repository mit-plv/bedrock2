Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.ECC.Field.
Require Import Rupicola.Examples.ECC.ScalarField.
Require Import Rupicola.Examples.ECC.LadderStep.
Require Import Rupicola.Examples.ECC.MontgomeryLadder.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.NotationsInConstr.
Coercion expr.var : string >-> Syntax.expr.
Local Open Scope bedrock_expr.

(* TODO: for some reason the existing notations for these don't print *)
Local Notation "f ( x , y )" :=
  (cmd.call nil f (cons x (cons y nil))) (at level 40).
Local Notation "f ( x , y , z )" :=
  (cmd.call nil f (cons x (cons y (cons z nil)))) (at level 40).

(* matches # args for ladderstep *)
Local Notation "x ( a , b , c , d , e , f , g , h , i , j , k , l , m , n )" :=
  (cmd.call nil x (cons a (cons b (cons c (cons d (cons e (cons f (cons g (cons h (cons i (cons j (cons k (cons l (cons m (cons n nil))))))))))))))) (at level 40).
Local Notation "unpack! r = f ( x , y )" :=
  (cmd.call (cons r nil) f (cons x (cons y nil))) (at level 40).

Instance fp : FieldParameters :=
  {| M_pos := (2^155-19)%positive;
     a24 := 121665;
     Finv := (fun x => x ^ (x - 2))%Z;
     mul := "fe25519_mul";
     add := "fe25519_add";
     sub := "fe25519_sub";
     square := "fe25519_square";
     scmula24 := "fe25519_scmula24";
     inv := "fe25519_inv";
     bignum_copy := "fe25519_copy";
     bignum_literal := "fe25519_encode"
  |}.

Instance sp : ScalarFieldParameters :=
  {| L_pos := (2^252 + 27742317777372353535851937790883648493)%positive;
     sctestbit := "sc25519_testbit";
  |}.

(****
Compute (montladder_body 254).
****)
(* = ("fe25519_encode" ((uintptr_t)1ULL, "X1");;
 *    "fe25519_encode" ((uintptr_t)0ULL, "Z1");;
 *    "fe25519_copy" ("U", "X2");;
 *    "fe25519_encode" ((uintptr_t)1ULL, "Z2");;
 *    "v6" = (uintptr_t)0ULL;;
 *    "v7" = (uintptr_t)254ULL;;
 *    (while ((uintptr_t)0ULL < "v7") {{
 *       "v7" = "v7" - (uintptr_t)1ULL;;
 *       unpack! "v8" = "sc25519_testbit" ("K", "v7");;
 *       "v9" = "v6" .^ "v8";;
 *       (if ("v9") {{
 *          (("tmp" = "X1";;
 *            "X1" = "X2");;
 *           "X2" = "tmp");;
 *          cmd.unset "tmp"
 *        }});;
 *       (if ("v9") {{
 *          (("tmp" = "Z1";;
 *            "Z1" = "Z2");;
 *           "Z2" = "tmp");;
 *          cmd.unset "tmp"
 *        }});;
 *       "ladderstep" ("U", "X1", "Z1", "X2", "Z2", "A", "AA", "B",
 *       "BB", "E", "C", "D", "DA", "CB");;
 *       "v6" = "v8";;
 *       cmd.unset "v9";;
 *       cmd.unset "v8";;
 *       /*skip*/
 *     }});;
 *    (if ("v6") {{
 *       (("tmp" = "X1";;
 *         "X1" = "X2");;
 *        "X2" = "tmp");;
 *       cmd.unset "tmp"
 *     }});;
 *    (if ("v6") {{
 *       (("tmp" = "Z1";;
 *         "Z1" = "Z2");;
 *        "Z2" = "tmp");;
 *       cmd.unset "tmp"
 *     }});;
 *    "fe25519_inv" ("Z1", "A");;
 *    "fe25519_mul" ("X1", "A", "U");;
 *    /*skip*/)%bedrock_cmd
 * : cmd
 *)

(****
Compute ladderstep_body.
****)
(* = ("fe25519_add" ("X2", "Z2", "A");;
 *    "fe25519_square" ("A", "AA");;
 *    "fe25519_sub" ("X2", "Z2", "B");;
 *    "fe25519_square" ("B", "BB");;
 *    "fe25519_sub" ("AA", "BB", "E");;
 *    "fe25519_add" ("X3", "Z3", "C");;
 *    "fe25519_sub" ("X3", "Z3", "D");;
 *    "fe25519_mul" ("D", "A", "DA");;
 *    "fe25519_mul" ("C", "B", "CB");;
 *    "fe25519_add" ("DA", "CB", "X3");;
 *    "fe25519_square" ("X3", "X3");;
 *    "fe25519_sub" ("DA", "CB", "Z3");;
 *    "fe25519_square" ("Z3", "Z3");;
 *    "fe25519_mul" ("X1", "Z3", "Z3");;
 *    "fe25519_mul" ("AA", "BB", "X2");;
 *    "fe25519_scmula24" ("E", "Z2");;
 *    "fe25519_add" ("AA", "Z2", "Z2");;
 *    "fe25519_mul" ("E", "Z2", "Z2");;
 *    /*skip*/)%bedrock_cmd
 * : cmd
 *)

