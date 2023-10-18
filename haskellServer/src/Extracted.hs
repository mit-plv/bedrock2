{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Extracted where
import Data.Char
import Data.Bits

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#if __GLASGOW_HASKELL__ >= 900
import qualified GHC.Exts
#endif
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
#if __GLASGOW_HASKELL__ >= 900
unsafeCoerce = GHC.Exts.unsafeCoerce#
#else
unsafeCoerce = GHC.Base.unsafeCoerce#
#endif
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

false_rect :: a1
false_rect =
  Prelude.error "absurd case"

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f _ =
  f

data Nat =
   O
 | S Nat

fst :: ((,) a1 a2) -> a1
fst p =
  case p of {
   (,) x _ -> x}

snd :: ((,) a1 a2) -> a2
snd p =
  case p of {
   (,) _ y -> y}

length :: (([]) a1) -> Nat
length l =
  case l of {
   ([]) -> O;
   (:) _ l' -> S (length l')}

app :: (([]) a1) -> (([]) a1) -> ([]) a1
app l m =
  case l of {
   ([]) -> m;
   (:) a l1 -> (:) a (app l1 m)}

data Comparison =
   Eq
 | Lt
 | Gt

compOpp :: Comparison -> Comparison
compOpp r =
  case r of {
   Eq -> Eq;
   Lt -> Gt;
   Gt -> Lt}

data SigT a p =
   ExistT a p

projT1 :: (SigT a1 a2) -> a1
projT1 x =
  case x of {
   ExistT a _ -> a}

projT2 :: (SigT a1 a2) -> a2
projT2 x =
  case x of {
   ExistT _ h -> h}

sumbool_rect :: (() -> a1) -> (() -> a1) -> Prelude.Bool -> a1
sumbool_rect f f0 s =
  case s of {
   Prelude.True -> f __;
   Prelude.False -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Prelude.Bool -> a1
sumbool_rec =
  sumbool_rect

data Uint =
   Nil
 | D0 Uint
 | D1 Uint
 | D2 Uint
 | D3 Uint
 | D4 Uint
 | D5 Uint
 | D6 Uint
 | D7 Uint
 | D8 Uint
 | D9 Uint

data Signed_int =
   Pos Uint
 | Neg Uint

revapp :: Uint -> Uint -> Uint
revapp d d' =
  case d of {
   Nil -> d';
   D0 d0 -> revapp d0 (D0 d');
   D1 d0 -> revapp d0 (D1 d');
   D2 d0 -> revapp d0 (D2 d');
   D3 d0 -> revapp d0 (D3 d');
   D4 d0 -> revapp d0 (D4 d');
   D5 d0 -> revapp d0 (D5 d');
   D6 d0 -> revapp d0 (D6 d');
   D7 d0 -> revapp d0 (D7 d');
   D8 d0 -> revapp d0 (D8 d');
   D9 d0 -> revapp d0 (D9 d')}

rev :: Uint -> Uint
rev d =
  revapp d Nil

double :: Uint -> Uint
double d =
  case d of {
   Nil -> Nil;
   D0 d0 -> D0 (double d0);
   D1 d0 -> D2 (double d0);
   D2 d0 -> D4 (double d0);
   D3 d0 -> D6 (double d0);
   D4 d0 -> D8 (double d0);
   D5 d0 -> D0 (succ_double d0);
   D6 d0 -> D2 (succ_double d0);
   D7 d0 -> D4 (succ_double d0);
   D8 d0 -> D6 (succ_double d0);
   D9 d0 -> D8 (succ_double d0)}

succ_double :: Uint -> Uint
succ_double d =
  case d of {
   Nil -> D1 Nil;
   D0 d0 -> D1 (double d0);
   D1 d0 -> D3 (double d0);
   D2 d0 -> D5 (double d0);
   D3 d0 -> D7 (double d0);
   D4 d0 -> D9 (double d0);
   D5 d0 -> D1 (succ_double d0);
   D6 d0 -> D3 (succ_double d0);
   D7 d0 -> D5 (succ_double d0);
   D8 d0 -> D7 (succ_double d0);
   D9 d0 -> D9 (succ_double d0)}

add :: Nat -> Nat -> Nat
add n m =
  case n of {
   O -> m;
   S p -> S (add p m)}

eqb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
eqb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False ->
    case b2 of {
     Prelude.True -> Prelude.False;
     Prelude.False -> Prelude.True}}

data N =
   N0
 | Npos Prelude.Integer

succ :: Prelude.Integer -> Prelude.Integer
succ x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> (\x -> 2 Prelude.* x) (succ p))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1) p)
    (\_ -> (\x -> 2 Prelude.* x) 1)
    x

add0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add0 x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x) (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (add0 p q))
      (\_ -> (\x -> 2 Prelude.* x) (succ p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (add0 p q))
      (\q -> (\x -> 2 Prelude.* x) (add0 p q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1) p)
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x) (succ q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) q)
      (\_ -> (\x -> 2 Prelude.* x) 1)
      y)
    x

add_carry :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add_carry x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x) (add_carry p q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1) (succ p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x) (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (add0 p q))
      (\_ -> (\x -> 2 Prelude.* x) (succ p))
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (succ q))
      (\q -> (\x -> 2 Prelude.* x) (succ q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1) 1)
      y)
    x

pred_double :: Prelude.Integer -> Prelude.Integer
pred_double x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) p))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1) (pred_double p))
    (\_ -> 1)
    x

pred_N :: Prelude.Integer -> N
pred_N x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> Npos ((\x -> 2 Prelude.* x) p))
    (\p -> Npos (pred_double p))
    (\_ -> N0)
    x

data Mask =
   IsNul
 | IsPos Prelude.Integer
 | IsNeg

succ_double_mask :: Mask -> Mask
succ_double_mask x =
  case x of {
   IsNul -> IsPos 1;
   IsPos p -> IsPos ((\x -> 2 Prelude.* x Prelude.+ 1) p);
   IsNeg -> IsNeg}

double_mask :: Mask -> Mask
double_mask x =
  case x of {
   IsPos p -> IsPos ((\x -> 2 Prelude.* x) p);
   x0 -> x0}

double_pred_mask :: Prelude.Integer -> Mask
double_pred_mask x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> IsPos ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) p)))
    (\p -> IsPos ((\x -> 2 Prelude.* x) (pred_double p)))
    (\_ -> IsNul)
    x

sub_mask :: Prelude.Integer -> Prelude.Integer -> Mask
sub_mask x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> double_mask (sub_mask p q))
      (\q -> succ_double_mask (sub_mask p q))
      (\_ -> IsPos ((\x -> 2 Prelude.* x) p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> succ_double_mask (sub_mask_carry p q))
      (\q -> double_mask (sub_mask p q))
      (\_ -> IsPos (pred_double p))
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\_ -> IsNeg)
      (\_ -> IsNeg)
      (\_ -> IsNul)
      y)
    x

sub_mask_carry :: Prelude.Integer -> Prelude.Integer -> Mask
sub_mask_carry x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> succ_double_mask (sub_mask_carry p q))
      (\q -> double_mask (sub_mask p q))
      (\_ -> IsPos (pred_double p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> double_mask (sub_mask_carry p q))
      (\q -> succ_double_mask (sub_mask_carry p q))
      (\_ -> double_pred_mask p)
      y)
    (\_ -> IsNeg)
    x

mul :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
mul x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> add0 y ((\x -> 2 Prelude.* x) (mul p y)))
    (\p -> (\x -> 2 Prelude.* x) (mul p y))
    (\_ -> y)
    x

iter :: (a1 -> a1) -> a1 -> Prelude.Integer -> a1
iter f x n =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\n' -> f (iter f (iter f x n') n'))
    (\n' -> iter f (iter f x n') n')
    (\_ -> f x)
    n

div2 :: Prelude.Integer -> Prelude.Integer
div2 p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 -> p0)
    (\p0 -> p0)
    (\_ -> 1)
    p

div2_up :: Prelude.Integer -> Prelude.Integer
div2_up p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 -> succ p0)
    (\p0 -> p0)
    (\_ -> 1)
    p

size :: Prelude.Integer -> Prelude.Integer
size p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 -> succ (size p0))
    (\p0 -> succ (size p0))
    (\_ -> 1)
    p

compare_cont :: Comparison -> Prelude.Integer -> Prelude.Integer ->
                Comparison
compare_cont r x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> compare_cont r p q)
      (\q -> compare_cont Gt p q)
      (\_ -> Gt)
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> compare_cont Lt p q)
      (\q -> compare_cont r p q)
      (\_ -> Gt)
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\_ -> Lt)
      (\_ -> Lt)
      (\_ -> r)
      y)
    x

compare :: Prelude.Integer -> Prelude.Integer -> Comparison
compare =
  compare_cont Eq

eqb0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
eqb0 p q =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q0 -> eqb0 p0 q0)
      (\_ -> Prelude.False)
      (\_ -> Prelude.False)
      q)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\_ -> Prelude.False)
      (\q0 -> eqb0 p0 q0)
      (\_ -> Prelude.False)
      q)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\_ -> Prelude.False)
      (\_ -> Prelude.False)
      (\_ -> Prelude.True)
      q)
    p

nsucc_double :: N -> N
nsucc_double x =
  case x of {
   N0 -> Npos 1;
   Npos p -> Npos ((\x -> 2 Prelude.* x Prelude.+ 1) p)}

ndouble :: N -> N
ndouble n =
  case n of {
   N0 -> N0;
   Npos p -> Npos ((\x -> 2 Prelude.* x) p)}

lor :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
lor p q =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q0 -> (\x -> 2 Prelude.* x Prelude.+ 1) (lor p0 q0))
      (\q0 -> (\x -> 2 Prelude.* x Prelude.+ 1) (lor p0 q0))
      (\_ -> p)
      q)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q0 -> (\x -> 2 Prelude.* x Prelude.+ 1) (lor p0 q0))
      (\q0 -> (\x -> 2 Prelude.* x) (lor p0 q0))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1) p0)
      q)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\_ -> q)
      (\q0 -> (\x -> 2 Prelude.* x Prelude.+ 1) q0)
      (\_ -> q)
      q)
    p

land :: Prelude.Integer -> Prelude.Integer -> N
land p q =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q0 -> nsucc_double (land p0 q0))
      (\q0 -> ndouble (land p0 q0))
      (\_ -> Npos 1)
      q)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q0 -> ndouble (land p0 q0))
      (\q0 -> ndouble (land p0 q0))
      (\_ -> N0)
      q)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\_ -> Npos 1)
      (\_ -> N0)
      (\_ -> Npos 1)
      q)
    p

ldiff :: Prelude.Integer -> Prelude.Integer -> N
ldiff p q =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q0 -> ndouble (ldiff p0 q0))
      (\q0 -> nsucc_double (ldiff p0 q0))
      (\_ -> Npos ((\x -> 2 Prelude.* x) p0))
      q)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q0 -> ndouble (ldiff p0 q0))
      (\q0 -> ndouble (ldiff p0 q0))
      (\_ -> Npos p)
      q)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\_ -> N0)
      (\_ -> Npos 1)
      (\_ -> N0)
      q)
    p

lxor :: Prelude.Integer -> Prelude.Integer -> N
lxor p q =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q0 -> ndouble (lxor p0 q0))
      (\q0 -> nsucc_double (lxor p0 q0))
      (\_ -> Npos ((\x -> 2 Prelude.* x) p0))
      q)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q0 -> nsucc_double (lxor p0 q0))
      (\q0 -> ndouble (lxor p0 q0))
      (\_ -> Npos ((\x -> 2 Prelude.* x Prelude.+ 1) p0))
      q)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q0 -> Npos ((\x -> 2 Prelude.* x) q0))
      (\q0 -> Npos ((\x -> 2 Prelude.* x Prelude.+ 1) q0))
      (\_ -> N0)
      q)
    p

iter_op :: (a1 -> a1 -> a1) -> Prelude.Integer -> a1 -> a1
iter_op op p a =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 -> op a (iter_op op p0 (op a a)))
    (\p0 -> iter_op op p0 (op a a))
    (\_ -> a)
    p

to_nat :: Prelude.Integer -> Nat
to_nat x =
  iter_op add x (S O)

of_succ_nat :: Nat -> Prelude.Integer
of_succ_nat n =
  case n of {
   O -> 1;
   S x -> succ (of_succ_nat x)}

to_little_uint :: Prelude.Integer -> Uint
to_little_uint p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 -> succ_double (to_little_uint p0))
    (\p0 -> double (to_little_uint p0))
    (\_ -> D1 Nil)
    p

to_uint :: Prelude.Integer -> Uint
to_uint p =
  rev (to_little_uint p)

compare0 :: N -> N -> Comparison
compare0 n m =
  case n of {
   N0 -> case m of {
          N0 -> Eq;
          Npos _ -> Lt};
   Npos n' -> case m of {
               N0 -> Gt;
               Npos m' -> compare n' m'}}

ltb :: N -> N -> Prelude.Bool
ltb x y =
  case compare0 x y of {
   Lt -> Prelude.True;
   _ -> Prelude.False}

succ_double0 :: N -> N
succ_double0 x =
  case x of {
   N0 -> Npos 1;
   Npos p -> Npos ((\x -> 2 Prelude.* x Prelude.+ 1) p)}

double0 :: N -> N
double0 n =
  case n of {
   N0 -> N0;
   Npos p -> Npos ((\x -> 2 Prelude.* x) p)}

succ_pos :: N -> Prelude.Integer
succ_pos n =
  case n of {
   N0 -> 1;
   Npos p -> succ p}

add1 :: N -> N -> N
add1 n m =
  case n of {
   N0 -> m;
   Npos p -> case m of {
              N0 -> n;
              Npos q -> Npos (add0 p q)}}

sub :: N -> N -> N
sub n m =
  case n of {
   N0 -> N0;
   Npos n' ->
    case m of {
     N0 -> n;
     Npos m' -> case sub_mask n' m' of {
                 IsPos p -> Npos p;
                 _ -> N0}}}

mul0 :: N -> N -> N
mul0 n m =
  case n of {
   N0 -> N0;
   Npos p -> case m of {
              N0 -> N0;
              Npos q -> Npos (mul p q)}}

compare1 :: N -> N -> Comparison
compare1 n m =
  case n of {
   N0 -> case m of {
          N0 -> Eq;
          Npos _ -> Lt};
   Npos n' -> case m of {
               N0 -> Gt;
               Npos m' -> compare n' m'}}

leb :: N -> N -> Prelude.Bool
leb x y =
  case compare1 x y of {
   Gt -> Prelude.False;
   _ -> Prelude.True}

pos_div_eucl :: Prelude.Integer -> N -> (,) N N
pos_div_eucl a b =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\a' ->
    case pos_div_eucl a' b of {
     (,) q r ->
      let {r' = succ_double0 r} in
      case leb b r' of {
       Prelude.True -> (,) (succ_double0 q) (sub r' b);
       Prelude.False -> (,) (double0 q) r'}})
    (\a' ->
    case pos_div_eucl a' b of {
     (,) q r ->
      let {r' = double0 r} in
      case leb b r' of {
       Prelude.True -> (,) (succ_double0 q) (sub r' b);
       Prelude.False -> (,) (double0 q) r'}})
    (\_ ->
    case b of {
     N0 -> (,) N0 (Npos 1);
     Npos p ->
      (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
        (\_ -> (,) N0 (Npos 1))
        (\_ -> (,) N0 (Npos 1))
        (\_ -> (,) (Npos 1) N0)
        p})
    a

lor0 :: N -> N -> N
lor0 n m =
  case n of {
   N0 -> m;
   Npos p -> case m of {
              N0 -> n;
              Npos q -> Npos (lor p q)}}

land0 :: N -> N -> N
land0 n m =
  case n of {
   N0 -> N0;
   Npos p -> case m of {
              N0 -> N0;
              Npos q -> land p q}}

ldiff0 :: N -> N -> N
ldiff0 n m =
  case n of {
   N0 -> N0;
   Npos p -> case m of {
              N0 -> n;
              Npos q -> ldiff p q}}

lxor0 :: N -> N -> N
lxor0 n m =
  case n of {
   N0 -> m;
   Npos p -> case m of {
              N0 -> n;
              Npos q -> lxor p q}}

concat :: (([]) (([]) a1)) -> ([]) a1
concat l =
  case l of {
   ([]) -> ([]);
   (:) x l0 -> app x (concat l0)}

map :: (a1 -> a2) -> (([]) a1) -> ([]) a2
map f l =
  case l of {
   ([]) -> ([]);
   (:) a t0 -> (:) (f a) (map f t0)}

flat_map :: (a1 -> ([]) a2) -> (([]) a1) -> ([]) a2
flat_map f l =
  case l of {
   ([]) -> ([]);
   (:) x t0 -> app (f x) (flat_map f t0)}

fold_left :: (a1 -> a2 -> a1) -> (([]) a2) -> a1 -> a1
fold_left f l a0 =
  case l of {
   ([]) -> a0;
   (:) b t0 -> fold_left f t0 (f a0 b)}

fold_right :: (a2 -> a1 -> a1) -> a1 -> (([]) a2) -> a1
fold_right f a0 l =
  case l of {
   ([]) -> a0;
   (:) b t0 -> f b (fold_right f a0 t0)}

find :: (a1 -> Prelude.Bool) -> (([]) a1) -> Prelude.Maybe a1
find f l =
  case l of {
   ([]) -> Prelude.Nothing;
   (:) x tl ->
    case f x of {
     Prelude.True -> Prelude.Just x;
     Prelude.False -> find f tl}}

repeat :: a1 -> Nat -> ([]) a1
repeat x n =
  case n of {
   O -> ([]);
   S k -> (:) x (repeat x k)}

double1 :: Prelude.Integer -> Prelude.Integer
double1 x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> 0)
    (\p -> (\x -> x) ((\x -> 2 Prelude.* x) p))
    (\p -> Prelude.negate ((\x -> 2 Prelude.* x) p))
    x

succ_double1 :: Prelude.Integer -> Prelude.Integer
succ_double1 x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> (\x -> x) 1)
    (\p -> (\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1) p))
    (\p -> Prelude.negate (pred_double p))
    x

pred_double0 :: Prelude.Integer -> Prelude.Integer
pred_double0 x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> Prelude.negate 1)
    (\p -> (\x -> x) (pred_double p))
    (\p -> Prelude.negate ((\x -> 2 Prelude.* x Prelude.+ 1) p))
    x

pos_sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pos_sub x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> double1 (pos_sub p q))
      (\q -> succ_double1 (pos_sub p q))
      (\_ -> (\x -> x) ((\x -> 2 Prelude.* x) p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> pred_double0 (pos_sub p q))
      (\q -> double1 (pos_sub p q))
      (\_ -> (\x -> x) (pred_double p))
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> Prelude.negate ((\x -> 2 Prelude.* x) q))
      (\q -> Prelude.negate (pred_double q))
      (\_ -> 0)
      y)
    x

opp :: Prelude.Integer -> Prelude.Integer
opp x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> 0)
    (\x0 -> Prelude.negate x0)
    (\x0 -> (\x -> x) x0)
    x

pred :: Prelude.Integer -> Prelude.Integer
pred x =
  (Prelude.+) x (Prelude.negate 1)

pow_pos :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pow_pos z =
  iter ((Prelude.*) z) ((\x -> x) 1)

pow :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pow x y =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> (\x -> x) 1)
    (\p -> pow_pos x p)
    (\_ -> 0)
    y

compare2 :: Prelude.Integer -> Prelude.Integer -> Comparison
compare2 x y =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> Eq)
      (\_ -> Lt)
      (\_ -> Gt)
      y)
    (\x' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> Gt)
      (\y' -> compare x' y')
      (\_ -> Gt)
      y)
    (\x' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> Lt)
      (\_ -> Lt)
      (\y' -> compOpp (compare x' y'))
      y)
    x

leb0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
leb0 x y =
  case compare2 x y of {
   Gt -> Prelude.False;
   _ -> Prelude.True}

ltb0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
ltb0 x y =
  case compare2 x y of {
   Lt -> Prelude.True;
   _ -> Prelude.False}

eqb1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
eqb1 x y =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> Prelude.True)
      (\_ -> Prelude.False)
      (\_ -> Prelude.False)
      y)
    (\p ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> Prelude.False)
      (\q -> eqb0 p q)
      (\_ -> Prelude.False)
      y)
    (\p ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> Prelude.False)
      (\_ -> Prelude.False)
      (\q -> eqb0 p q)
      y)
    x

to_nat0 :: Prelude.Integer -> Nat
to_nat0 z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> O)
    (\p -> to_nat p)
    (\_ -> O)
    z

of_nat :: Nat -> Prelude.Integer
of_nat n =
  case n of {
   O -> 0;
   S n0 -> (\x -> x) (of_succ_nat n0)}

of_N :: N -> Prelude.Integer
of_N n =
  case n of {
   N0 -> 0;
   Npos p -> (\x -> x) p}

to_int :: Prelude.Integer -> Signed_int
to_int n =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> Pos (D0 Nil))
    (\p -> Pos (to_uint p))
    (\p -> Neg (to_uint p))
    n

pos_div_eucl0 :: Prelude.Integer -> Prelude.Integer -> (,) Prelude.Integer
                 Prelude.Integer
pos_div_eucl0 a b =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\a' ->
    case pos_div_eucl0 a' b of {
     (,) q r ->
      let {
       r' = (Prelude.+) ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) r)
              ((\x -> x) 1)}
      in
      case ltb0 r' b of {
       Prelude.True -> (,)
        ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q) r';
       Prelude.False -> (,)
        ((Prelude.+) ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q)
          ((\x -> x) 1)) ((Prelude.-) r' b)}})
    (\a' ->
    case pos_div_eucl0 a' b of {
     (,) q r ->
      let {r' = (Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) r} in
      case ltb0 r' b of {
       Prelude.True -> (,)
        ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q) r';
       Prelude.False -> (,)
        ((Prelude.+) ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q)
          ((\x -> x) 1)) ((Prelude.-) r' b)}})
    (\_ ->
    case leb0 ((\x -> x) ((\x -> 2 Prelude.* x) 1)) b of {
     Prelude.True -> (,) 0 ((\x -> x) 1);
     Prelude.False -> (,) ((\x -> x) 1) 0})
    a

div_eucl :: Prelude.Integer -> Prelude.Integer -> (,) Prelude.Integer
            Prelude.Integer
div_eucl a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> (,) 0 0)
    (\a' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> (,) 0 a)
      (\_ -> pos_div_eucl0 a' b)
      (\b' ->
      case pos_div_eucl0 a' ((\x -> x) b') of {
       (,) q r ->
        (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
          (\_ -> (,) (opp q) 0)
          (\_ -> (,) (opp ((Prelude.+) q ((\x -> x) 1)))
          ((Prelude.+) b r))
          (\_ -> (,) (opp ((Prelude.+) q ((\x -> x) 1))) ((Prelude.+) b r))
          r})
      b)
    (\a' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> (,) 0 a)
      (\_ ->
      case pos_div_eucl0 a' b of {
       (,) q r ->
        (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
          (\_ -> (,) (opp q) 0)
          (\_ -> (,) (opp ((Prelude.+) q ((\x -> x) 1)))
          ((Prelude.-) b r))
          (\_ -> (,) (opp ((Prelude.+) q ((\x -> x) 1))) ((Prelude.-) b r))
          r})
      (\b' ->
      case pos_div_eucl0 a' ((\x -> x) b') of {
       (,) q r -> (,) q (opp r)})
      b)
    a

div :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
div = (\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)

modulo :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
modulo = (\n m -> if m Prelude.== 0 then n else Prelude.mod n m)

quotrem :: Prelude.Integer -> Prelude.Integer -> (,) Prelude.Integer
           Prelude.Integer
quotrem a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> (,) 0 0)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> (,) 0 a)
      (\b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       (,) q r -> (,) (of_N q) (of_N r)})
      (\b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       (,) q r -> (,) (opp (of_N q)) (of_N r)})
      b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> (,) 0 a)
      (\b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       (,) q r -> (,) (opp (of_N q)) (opp (of_N r))})
      (\b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       (,) q r -> (,) (of_N q) (opp (of_N r))})
      b)
    a

quot :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
quot a b =
  fst (quotrem a b)

rem :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
rem a b =
  snd (quotrem a b)

div0 :: Prelude.Integer -> Prelude.Integer
div0 z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> 0)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\_ -> (\x -> x) (div2 p))
      (\_ -> (\x -> x) (div2 p))
      (\_ -> 0)
      p)
    (\p -> Prelude.negate (div2_up p))
    z

log2 :: Prelude.Integer -> Prelude.Integer
log2 z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> 0)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\p -> (\x -> x) (size p))
      (\p -> (\x -> x) (size p))
      (\_ -> 0)
      p0)
    (\_ -> 0)
    z

shiftl :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
shiftl a n =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> a)
    (\p ->
    iter ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1))) a p)
    (\p -> iter div0 a p)
    n

shiftr :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
shiftr a n =
  shiftl a (opp n)

lor1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
lor1 a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> a)
      (\b0 -> (\x -> x) (lor a0 b0))
      (\b0 -> Prelude.negate (succ_pos (ldiff0 (pred_N b0) (Npos a0))))
      b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> a)
      (\b0 -> Prelude.negate
      (succ_pos (ldiff0 (pred_N a0) (Npos b0))))
      (\b0 -> Prelude.negate (succ_pos (land0 (pred_N a0) (pred_N b0))))
      b)
    a

land1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
land1 a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> 0)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> 0)
      (\b0 -> of_N (land a0 b0))
      (\b0 -> of_N (ldiff0 (Npos a0) (pred_N b0)))
      b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> 0)
      (\b0 -> of_N (ldiff0 (Npos b0) (pred_N a0)))
      (\b0 -> Prelude.negate (succ_pos (lor0 (pred_N a0) (pred_N b0))))
      b)
    a

ldiff1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
ldiff1 a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> 0)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> a)
      (\b0 -> of_N (ldiff a0 b0))
      (\b0 -> of_N (land0 (Npos a0) (pred_N b0)))
      b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> a)
      (\b0 -> Prelude.negate (succ_pos (lor0 (pred_N a0) (Npos b0))))
      (\b0 -> of_N (ldiff0 (pred_N b0) (pred_N a0)))
      b)
    a

lxor1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
lxor1 a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> a)
      (\b0 -> of_N (lxor a0 b0))
      (\b0 -> Prelude.negate (succ_pos (lxor0 (Npos a0) (pred_N b0))))
      b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> a)
      (\b0 -> Prelude.negate (succ_pos (lxor0 (pred_N a0) (Npos b0))))
      (\b0 -> of_N (lxor0 (pred_N a0) (pred_N b0)))
      b)
    a

lnot :: Prelude.Integer -> Prelude.Integer
lnot a =
  pred (opp a)

n_of_digits :: (([]) Prelude.Bool) -> N
n_of_digits l =
  case l of {
   ([]) -> N0;
   (:) b l' ->
    add1 (case b of {
           Prelude.True -> Npos 1;
           Prelude.False -> N0})
      (mul0 (Npos ((\x -> 2 Prelude.* x) 1)) (n_of_digits l'))}

n_of_ascii :: Prelude.Char -> N
n_of_ascii a =
  (\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0)
              (Data.Bits.testBit (Data.Char.ord a) 1)
              (Data.Bits.testBit (Data.Char.ord a) 2)
              (Data.Bits.testBit (Data.Char.ord a) 3)
              (Data.Bits.testBit (Data.Char.ord a) 4)
              (Data.Bits.testBit (Data.Char.ord a) 5)
              (Data.Bits.testBit (Data.Char.ord a) 6)
              (Data.Bits.testBit (Data.Char.ord a) 7))
    (\a0 a1 a2 a3 a4 a5 a6 a7 ->
    n_of_digits ((:) a0 ((:) a1 ((:) a2 ((:) a3 ((:) a4 ((:) a5 ((:) a6 ((:)
      a7 ([]))))))))))
    a

append :: Prelude.String -> Prelude.String -> Prelude.String
append s1 s2 =
  case s1 of {
   ([]) -> s2;
   (:) c s1' -> (:) c (append s1' s2)}

length0 :: Prelude.String -> Nat
length0 s =
  case s of {
   ([]) -> O;
   (:) _ s' -> S (length0 s')}

data Map key value =
   Mk (Any -> key -> Prelude.Maybe value) Any (Any -> key -> value -> Any) 
 (Any -> key -> Any) (() -> (Any -> key -> value -> Any) -> Any -> Any ->
                     Any)

type Rep key value = Any

get :: (Map a1 a2) -> (Rep a1 a2) -> a1 -> Prelude.Maybe a2
get map2 =
  case map2 of {
   Mk get0 _ _ _ _ -> get0}

empty :: (Map a1 a2) -> Rep a1 a2
empty map2 =
  case map2 of {
   Mk _ empty0 _ _ _ -> empty0}

put :: (Map a1 a2) -> (Rep a1 a2) -> a1 -> a2 -> Rep a1 a2
put map2 =
  case map2 of {
   Mk _ _ put1 _ _ -> put1}

remove :: (Map a1 a2) -> (Rep a1 a2) -> a1 -> Rep a1 a2
remove map2 =
  case map2 of {
   Mk _ _ _ remove1 _ -> remove1}

update :: (Map a1 a2) -> (Rep a1 a2) -> a1 -> (Prelude.Maybe a2) -> Rep a1 a2
update map2 m k ov =
  case ov of {
   Prelude.Just v -> put map2 m k v;
   Prelude.Nothing -> remove map2 m k}

of_list :: (Map a1 a2) -> (([]) ((,) a1 a2)) -> Rep a1 a2
of_list map2 l =
  case l of {
   ([]) -> empty map2;
   (:) p l0 -> case p of {
                (,) k v -> put map2 (of_list map2 l0) k v}}

type Parameters =
  Any -> Any -> Prelude.Bool
  -- singleton inductive, whose constructor was Build_parameters
  
type Key = Any

type Value = Any

ltb1 :: Parameters -> Key -> Key -> Prelude.Bool
ltb1 parameters =
  parameters

eqb2 :: Parameters -> Key -> Key -> Prelude.Bool
eqb2 p k1 k2 =
  (Prelude.&&) (Prelude.not (ltb1 p k1 k2)) (Prelude.not (ltb1 p k2 k1))

put0 :: Parameters -> (([]) ((,) Key Value)) -> Key -> Value -> ([])
        ((,) Key Value)
put0 p m k v =
  case m of {
   ([]) -> (:) ((,) k v) ([]);
   (:) y m' ->
    case y of {
     (,) k' v' ->
      case ltb1 p k k' of {
       Prelude.True -> (:) ((,) k v) m;
       Prelude.False ->
        case ltb1 p k' k of {
         Prelude.True -> (:) ((,) k' v') (put0 p m' k v);
         Prelude.False -> (:) ((,) k v) m'}}}}

remove0 :: Parameters -> (([]) ((,) Key Value)) -> Key -> ([])
           ((,) Key Value)
remove0 p m k =
  case m of {
   ([]) -> ([]);
   (:) y m' ->
    case y of {
     (,) k' v' ->
      case ltb1 p k k' of {
       Prelude.True -> m;
       Prelude.False ->
        case ltb1 p k' k of {
         Prelude.True -> (:) ((,) k' v') (remove0 p m' k);
         Prelude.False -> m'}}}}

type Rep0 =
  ([]) ((,) Key Value)
  -- singleton inductive, whose constructor was Build_rep
  
value :: Parameters -> Rep0 -> ([]) ((,) Key Value)
value _ r =
  r

lookup :: Parameters -> (([]) ((,) Key Value)) -> Key -> Prelude.Maybe Value
lookup p l k =
  case find (\p0 -> eqb2 p k (fst p0)) l of {
   Prelude.Just p0 -> case p0 of {
                       (,) _ v -> Prelude.Just v};
   Prelude.Nothing -> Prelude.Nothing}

map0 :: Parameters -> Map Key Value
map0 p =
  let {wrapped_put = \m k v -> put0 p (value p m) k v} in
  let {wrapped_remove = \m k -> remove0 p (value p m) k} in
  Mk (\m k -> lookup p (value p (unsafeCoerce m)) k) (unsafeCoerce ([]))
  (unsafeCoerce wrapped_put) (unsafeCoerce wrapped_remove) (\_ f r0 m ->
  fold_right (\pat r -> case pat of {
                         (,) k v -> f r k v}) r0 (value p (unsafeCoerce m)))

ltb2 :: Prelude.Char -> Prelude.Char -> Prelude.Bool
ltb2 c d =
  ltb (n_of_ascii c) (n_of_ascii d)

ltb3 :: Prelude.String -> Prelude.String -> Prelude.Bool
ltb3 a b =
  case a of {
   ([]) -> case b of {
            ([]) -> Prelude.False;
            (:) _ _ -> Prelude.True};
   (:) x a' ->
    case b of {
     ([]) -> Prelude.False;
     (:) y b' ->
      case ((Prelude.==) :: Prelude.Char -> Prelude.Char -> Prelude.Bool) x y of {
       Prelude.True -> ltb3 a' b';
       Prelude.False -> ltb2 x y}}}

build_parameters :: Parameters
build_parameters =
  unsafeCoerce ltb3

map1 :: Map Key Value
map1 =
  map0 build_parameters

data Word =
   Build_word (Any -> Prelude.Integer) (Any -> Prelude.Integer) (Prelude.Integer
                                                                -> Any) 
 (Any -> Any -> Any) (Any -> Any -> Any) (Any -> Any) (Any -> Any -> Any) 
 (Any -> Any -> Any) (Any -> Any -> Any) (Any -> Any) (Any -> Any -> Any) 
 (Any -> Any -> Any) (Any -> Any -> Any) (Any -> Any -> Any) (Any -> Any ->
                                                             Any) (Any -> Any
                                                                  -> Any) 
 (Any -> Any -> Any) (Any -> Any -> Any) (Any -> Any -> Any) (Any -> Any ->
                                                             Any) (Any -> Any
                                                                  -> Any) 
 (Any -> Any -> Any) (Any -> Any -> Prelude.Bool) (Any -> Any ->
                                                  Prelude.Bool) (Any -> Any
                                                                ->
                                                                Prelude.Bool) 
 (Prelude.Integer -> Any -> Any)

type Rep1 = Any

unsigned :: Prelude.Integer -> Word -> Rep1 -> Prelude.Integer
unsigned _ word0 =
  case word0 of {
   Build_word unsigned1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
    unsigned1}

of_Z :: Prelude.Integer -> Word -> Prelude.Integer -> Rep1
of_Z _ word0 =
  case word0 of {
   Build_word _ _ of_Z0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
    of_Z0}

add2 :: Prelude.Integer -> Word -> Rep1 -> Rep1 -> Rep1
add2 _ word0 =
  case word0 of {
   Build_word _ _ _ add3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> add3}

sub0 :: Prelude.Integer -> Word -> Rep1 -> Rep1 -> Rep1
sub0 _ word0 =
  case word0 of {
   Build_word _ _ _ _ sub1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> sub1}

opp0 :: Prelude.Integer -> Word -> Rep1 -> Rep1
opp0 _ word0 =
  case word0 of {
   Build_word _ _ _ _ _ opp1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> opp1}

mul1 :: Prelude.Integer -> Word -> Rep1 -> Rep1 -> Rep1
mul1 _ word0 =
  case word0 of {
   Build_word _ _ _ _ _ _ _ _ _ _ _ mul2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> mul2}

divu :: Prelude.Integer -> Word -> Rep1 -> Rep1 -> Rep1
divu _ word0 =
  case word0 of {
   Build_word _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ divu0 _ _ _ _ _ _ _ _ _ _ ->
    divu0}

divs :: Prelude.Integer -> Word -> Rep1 -> Rep1 -> Rep1
divs _ word0 =
  case word0 of {
   Build_word _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ divs0 _ _ _ _ _ _ _ _ _ ->
    divs0}

modu :: Prelude.Integer -> Word -> Rep1 -> Rep1 -> Rep1
modu _ word0 =
  case word0 of {
   Build_word _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ modu0 _ _ _ _ _ _ _ _ ->
    modu0}

mods :: Prelude.Integer -> Word -> Rep1 -> Rep1 -> Rep1
mods _ word0 =
  case word0 of {
   Build_word _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mods0 _ _ _ _ _ _ _ ->
    mods0}

eqb3 :: Prelude.Integer -> Word -> Rep1 -> Rep1 -> Prelude.Bool
eqb3 _ word0 =
  case word0 of {
   Build_word _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eqb4 _ _ _ -> eqb4}

ltu :: Prelude.Integer -> Word -> Rep1 -> Rep1 -> Prelude.Bool
ltu _ word0 =
  case word0 of {
   Build_word _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ltu0 _ _ -> ltu0}

lts :: Prelude.Integer -> Word -> Rep1 -> Rep1 -> Prelude.Bool
lts _ word0 =
  case word0 of {
   Build_word _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lts0 _ -> lts0}

cast :: a1 -> a1 -> a2 -> a2
cast t1 t2 x =
  eq_rect t1 x t2

data Type =
   TWord
 | TInt
 | TBool
 | TString
 | TPair Prelude.String Type Type
 | TEmpty
 | TList Type

type_rect :: a1 -> a1 -> a1 -> a1 -> (Prelude.String -> Type -> a1 -> Type ->
             a1 -> a1) -> a1 -> (Type -> a1 -> a1) -> Type -> a1
type_rect f f0 f1 f2 f3 f4 f5 t0 =
  case t0 of {
   TWord -> f;
   TInt -> f0;
   TBool -> f1;
   TString -> f2;
   TPair s t1 t2 ->
    f3 s t1 (type_rect f f0 f1 f2 f3 f4 f5 t1) t2
      (type_rect f f0 f1 f2 f3 f4 f5 t2);
   TEmpty -> f4;
   TList t1 -> f5 t1 (type_rect f f0 f1 f2 f3 f4 f5 t1)}

type_rec :: a1 -> a1 -> a1 -> a1 -> (Prelude.String -> Type -> a1 -> Type ->
            a1 -> a1) -> a1 -> (Type -> a1 -> a1) -> Type -> a1
type_rec =
  type_rect

can_eq :: Type -> Prelude.Bool
can_eq t0 =
  case t0 of {
   TPair _ _ _ -> Prelude.False;
   TList _ -> Prelude.False;
   _ -> Prelude.True}

type_eq_dec :: Type -> Type -> Prelude.Bool
type_eq_dec t1 t2 =
  type_rec (\x -> case x of {
                   TWord -> Prelude.True;
                   _ -> Prelude.False}) (\x ->
    case x of {
     TInt -> Prelude.True;
     _ -> Prelude.False}) (\x ->
    case x of {
     TBool -> Prelude.True;
     _ -> Prelude.False}) (\x ->
    case x of {
     TString -> Prelude.True;
     _ -> Prelude.False}) (\s _ h _ h0 x ->
    case x of {
     TPair s0 t3 t4 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ ->
          sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (h0 t4))
          (\_ -> Prelude.False) (h t3)) (\_ -> Prelude.False)
        (((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) s
          s0);
     _ -> Prelude.False}) (\x ->
    case x of {
     TEmpty -> Prelude.True;
     _ -> Prelude.False}) (\_ h x ->
    case x of {
     TList t0 ->
      sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (h t0);
     _ -> Prelude.False}) t1 t2

data Patom =
   PAWord Prelude.Integer
 | PAInt Prelude.Integer
 | PABool Prelude.Bool
 | PAString Prelude.String
 | PANil Type

data Atom =
   AWord Prelude.Integer
 | AInt Prelude.Integer
 | ABool Prelude.Bool
 | AString Prelude.String
 | ANil Type
 | AEmpty

data Punop =
   PONeg
 | PONot
 | POLength
 | POIntToString

data Unop =
   OWNeg
 | ONeg
 | ONot
 | OLength Type
 | OLengthString
 | OFst Prelude.String Type Type
 | OSnd Prelude.String Type Type
 | OIntToString

data Pbinop =
   POPlus
 | POMinus
 | POTimes
 | PODivU
 | PODiv
 | POModU
 | POMod
 | POAnd
 | POOr
 | POConcat
 | POLessU
 | POLess
 | POEq
 | PORepeat
 | POPair
 | POCons
 | PORange

data Binop =
   OWPlus
 | OPlus
 | OWMinus
 | OMinus
 | OWTimes
 | OTimes
 | OWDivU
 | OWDivS
 | ODiv
 | OWModU
 | OWModS
 | OMod
 | OAnd
 | OOr
 | OConcat Type
 | OConcatString
 | OWLessU
 | OWLessS
 | OLess
 | OEq Type
 | ORepeat Type
 | OPair Prelude.String Type Type
 | OCons Type
 | ORange
 | OWRange

data Expr =
   EVar Type Prelude.String
 | ELoc Type Prelude.String
 | EAtom Type Atom
 | EUnop Type Type Unop Expr
 | EBinop Type Type Type Binop Expr Expr
 | EFlatmap Type Type Expr Prelude.String Expr
 | EFold Type Type Expr Expr Prelude.String Prelude.String Expr
 | EIf Type Expr Expr Expr
 | ELet Type Type Prelude.String Expr Expr

data Pexpr =
   PEVar Prelude.String
 | PEAtom Patom
 | PESingleton Pexpr
 | PEUnop Punop Pexpr
 | PEBinop Pbinop Pexpr Pexpr
 | PEFlatmap Pexpr Prelude.String Pexpr
 | PEFold Pexpr Pexpr Prelude.String Prelude.String Pexpr
 | PEIf Pexpr Pexpr Pexpr
 | PELet Prelude.String Pexpr Pexpr
 | PERecord (([]) ((,) Prelude.String Pexpr))
 | PEProj Pexpr Prelude.String
 | PEElaborated Type Expr

data Command =
   CSkip
 | CSeq Command Command
 | CLet Type Prelude.String Expr Command
 | CLetMut Type Prelude.String Expr Command
 | CGets Type Prelude.String Expr
 | CIf Expr Command Command
 | CForeach Type Prelude.String Expr Command

data Pcommand =
   PCSkip
 | PCSeq Pcommand Pcommand
 | PCLet Prelude.String Pexpr Pcommand
 | PCLetMut Prelude.String Pexpr Pcommand
 | PCGets Prelude.String Pexpr
 | PCIf Pexpr Pcommand Pcommand
 | PCForeach Prelude.String Pexpr Pcommand

data Dlist =
   Dnil
 | Dcons Any Dlist

data Result a =
   Success a
 | Failure Dlist

enforce_type :: Type -> Type -> Expr -> Result Expr
enforce_type t1 t2 e =
  case type_eq_dec t2 t1 of {
   Prelude.True -> Success (cast t2 t1 e);
   Prelude.False -> Failure (Dcons (unsafeCoerce e) (Dcons
    (unsafeCoerce "has type") (Dcons (unsafeCoerce t2) (Dcons
    (unsafeCoerce "but expected") (Dcons (unsafeCoerce t1) Dnil)))))}

elaborate_atom :: Patom -> Result (SigT Type Expr)
elaborate_atom pa =
  case pa of {
   PAWord z -> Success (ExistT TWord (EAtom TWord (AWord z)));
   PAInt z -> Success (ExistT TInt (EAtom TInt (AInt z)));
   PABool b -> Success (ExistT TBool (EAtom TBool (ABool b)));
   PAString s -> Success (ExistT TString (EAtom TString (AString s)));
   PANil t0 -> Success (ExistT (TList t0) (EAtom (TList t0) (ANil t0)))}

elaborate_unop :: Punop -> Type -> Expr -> Result (SigT Type Expr)
elaborate_unop po t0 e =
  case po of {
   PONeg ->
    case t0 of {
     TWord -> Success (ExistT TWord (EUnop TWord TWord OWNeg e));
     TInt -> Success (ExistT TInt (EUnop TInt TInt ONeg e));
     _ -> Failure (Dcons (unsafeCoerce e) (Dcons (unsafeCoerce "has type")
      (Dcons (unsafeCoerce t0) (Dcons (unsafeCoerce "but expected") (Dcons
      (unsafeCoerce TWord) (Dcons (unsafeCoerce "or") (Dcons
      (unsafeCoerce TInt) Dnil)))))))};
   PONot ->
    case enforce_type TBool t0 e of {
     Success e' -> Success (ExistT TBool (EUnop TBool TBool ONot e'));
     Failure e0 -> Failure e0};
   POLength ->
    case t0 of {
     TString -> Success (ExistT TInt (EUnop TString TInt OLengthString e));
     TList t1 -> Success (ExistT TInt (EUnop (TList t1) TInt (OLength t1) e));
     _ -> Failure (Dcons (unsafeCoerce e) (Dcons (unsafeCoerce "has type")
      (Dcons (unsafeCoerce t0) (Dcons (unsafeCoerce "but expected") (Dcons
      (unsafeCoerce (\x -> TList x)) (Dcons (unsafeCoerce "or") (Dcons
      (unsafeCoerce TString) Dnil)))))))};
   POIntToString ->
    case enforce_type TInt t0 e of {
     Success e' -> Success (ExistT TString (EUnop TInt TString OIntToString
      e'));
     Failure e0 -> Failure e0}}

construct_eq' :: Type -> Expr -> Expr -> Any
construct_eq' t0 e1 e2 =
  case t0 of {
   TBool -> unsafeCoerce (EBinop TBool TBool TBool (OEq TBool) e1 e2);
   TPair _ _ _ -> unsafeCoerce ();
   TList _ -> unsafeCoerce ();
   x -> unsafeCoerce (EBinop x x TBool (OEq x) e1 e2)}

construct_eq :: Type -> Expr -> Expr -> Result (SigT Type Expr)
construct_eq t0 e1 e2 =
  let {b = can_eq t0} in
  case b of {
   Prelude.True ->
    let {e = construct_eq' t0 e1 e2} in
    let {e0 = eq_rect (can_eq t0) e Prelude.True} in
    Success (ExistT TBool (unsafeCoerce e0));
   Prelude.False -> Failure (Dcons (unsafeCoerce e1) (Dcons
    (unsafeCoerce "has type") (Dcons (unsafeCoerce t0) (Dcons
    (unsafeCoerce "which does not support equality") Dnil))))}

elaborate_binop :: Pbinop -> Type -> Type -> Expr -> Expr -> Result
                   (SigT Type Expr)
elaborate_binop po t1 t2 e1 e2 =
  case po of {
   POPlus ->
    case t1 of {
     TWord ->
      case enforce_type TWord t2 e2 of {
       Success e2' -> Success (ExistT TWord (EBinop TWord TWord TWord OWPlus
        e1 e2'));
       Failure e -> Failure e};
     TInt ->
      case enforce_type TInt t2 e2 of {
       Success e2' -> Success (ExistT TInt (EBinop TInt TInt TInt OPlus e1
        e2'));
       Failure e -> Failure e};
     _ -> Failure (Dcons (unsafeCoerce e1) (Dcons (unsafeCoerce "has type")
      (Dcons (unsafeCoerce t1) (Dcons (unsafeCoerce "but expected") (Dcons
      (unsafeCoerce TWord) (Dcons (unsafeCoerce "or") (Dcons
      (unsafeCoerce TInt) Dnil)))))))};
   POMinus ->
    case t1 of {
     TWord ->
      case enforce_type TWord t2 e2 of {
       Success e2' -> Success (ExistT TWord (EBinop TWord TWord TWord OWMinus
        e1 e2'));
       Failure e -> Failure e};
     TInt ->
      case enforce_type TInt t2 e2 of {
       Success e2' -> Success (ExistT TInt (EBinop TInt TInt TInt OMinus e1
        e2'));
       Failure e -> Failure e};
     _ -> Failure (Dcons (unsafeCoerce e1) (Dcons (unsafeCoerce "has type")
      (Dcons (unsafeCoerce t1) (Dcons (unsafeCoerce "but expected") (Dcons
      (unsafeCoerce TWord) (Dcons (unsafeCoerce "or") (Dcons
      (unsafeCoerce TInt) Dnil)))))))};
   POTimes ->
    case t1 of {
     TWord ->
      case enforce_type TWord t2 e2 of {
       Success e2' -> Success (ExistT TWord (EBinop TWord TWord TWord OWTimes
        e1 e2'));
       Failure e -> Failure e};
     TInt ->
      case enforce_type TInt t2 e2 of {
       Success e2' -> Success (ExistT TInt (EBinop TInt TInt TInt OTimes e1
        e2'));
       Failure e -> Failure e};
     _ -> Failure (Dcons (unsafeCoerce e1) (Dcons (unsafeCoerce "has type")
      (Dcons (unsafeCoerce t1) (Dcons (unsafeCoerce "but expected") (Dcons
      (unsafeCoerce TWord) (Dcons (unsafeCoerce "or") (Dcons
      (unsafeCoerce TInt) Dnil)))))))};
   PODivU ->
    case enforce_type TWord t1 e1 of {
     Success e1' ->
      case enforce_type TWord t2 e2 of {
       Success e2' -> Success (ExistT TWord (EBinop TWord TWord TWord OWDivU
        e1' e2'));
       Failure e -> Failure e};
     Failure e -> Failure e};
   PODiv ->
    case t1 of {
     TWord ->
      case enforce_type TWord t2 e2 of {
       Success e2' -> Success (ExistT TWord (EBinop TWord TWord TWord OWDivS
        e1 e2'));
       Failure e -> Failure e};
     TInt ->
      case enforce_type TInt t2 e2 of {
       Success e2' -> Success (ExistT TInt (EBinop TInt TInt TInt ODiv e1
        e2'));
       Failure e -> Failure e};
     _ -> Failure (Dcons (unsafeCoerce e1) (Dcons (unsafeCoerce "has type")
      (Dcons (unsafeCoerce t1) (Dcons (unsafeCoerce "but expected") (Dcons
      (unsafeCoerce TWord) (Dcons (unsafeCoerce "or") (Dcons
      (unsafeCoerce TInt) Dnil)))))))};
   POModU ->
    case enforce_type TWord t1 e1 of {
     Success e1' ->
      case enforce_type TWord t2 e2 of {
       Success e2' -> Success (ExistT TWord (EBinop TWord TWord TWord OWModU
        e1' e2'));
       Failure e -> Failure e};
     Failure e -> Failure e};
   POMod ->
    case t1 of {
     TWord ->
      case enforce_type TWord t2 e2 of {
       Success e2' -> Success (ExistT TWord (EBinop TWord TWord TWord OWModS
        e1 e2'));
       Failure e -> Failure e};
     TInt ->
      case enforce_type TInt t2 e2 of {
       Success e2' -> Success (ExistT TInt (EBinop TInt TInt TInt OMod e1
        e2'));
       Failure e -> Failure e};
     _ -> Failure (Dcons (unsafeCoerce e1) (Dcons (unsafeCoerce "has type")
      (Dcons (unsafeCoerce t1) (Dcons (unsafeCoerce "but expected") (Dcons
      (unsafeCoerce TWord) (Dcons (unsafeCoerce "or") (Dcons
      (unsafeCoerce TInt) Dnil)))))))};
   POAnd ->
    case enforce_type TBool t1 e1 of {
     Success e1' ->
      case enforce_type TBool t2 e2 of {
       Success e2' -> Success (ExistT TBool (EBinop TBool TBool TBool OAnd
        e1' e2'));
       Failure e -> Failure e};
     Failure e -> Failure e};
   POOr ->
    case enforce_type TBool t1 e1 of {
     Success e1' ->
      case enforce_type TBool t2 e2 of {
       Success e2' -> Success (ExistT TBool (EBinop TBool TBool TBool OOr e1'
        e2'));
       Failure e -> Failure e};
     Failure e -> Failure e};
   POConcat ->
    case t1 of {
     TString ->
      case enforce_type TString t2 e2 of {
       Success e2' -> Success (ExistT TString (EBinop TString TString TString
        OConcatString e1 e2'));
       Failure e -> Failure e};
     TList t3 ->
      case enforce_type (TList t3) t2 e2 of {
       Success e2' -> Success (ExistT (TList t3) (EBinop (TList t3) (TList
        t3) (TList t3) (OConcat t3) e1 e2'));
       Failure e -> Failure e};
     _ -> Failure (Dcons (unsafeCoerce e1) (Dcons (unsafeCoerce "has type")
      (Dcons (unsafeCoerce t1) (Dcons (unsafeCoerce "but expected") (Dcons
      (unsafeCoerce (\x -> TList x)) (Dcons (unsafeCoerce "or") (Dcons
      (unsafeCoerce TString) Dnil)))))))};
   POLessU ->
    case enforce_type TWord t1 e1 of {
     Success e1' ->
      case enforce_type TWord t2 e2 of {
       Success e2' -> Success (ExistT TBool (EBinop TWord TWord TBool OWLessU
        e1' e2'));
       Failure e -> Failure e};
     Failure e -> Failure e};
   POLess ->
    case t1 of {
     TWord ->
      case enforce_type TWord t2 e2 of {
       Success e2' -> Success (ExistT TBool (EBinop TWord TWord TBool OWLessU
        e1 e2'));
       Failure e -> Failure e};
     TInt ->
      case enforce_type TInt t2 e2 of {
       Success e2' -> Success (ExistT TBool (EBinop TInt TInt TBool OLess e1
        e2'));
       Failure e -> Failure e};
     _ -> Failure (Dcons (unsafeCoerce e1) (Dcons (unsafeCoerce "has type")
      (Dcons (unsafeCoerce t1) (Dcons (unsafeCoerce "but expected") (Dcons
      (unsafeCoerce TWord) (Dcons (unsafeCoerce "or") (Dcons
      (unsafeCoerce TInt) Dnil)))))))};
   POEq ->
    case enforce_type t1 t2 e2 of {
     Success e2' -> construct_eq t1 e1 e2';
     Failure e -> Failure e};
   PORepeat ->
    case t1 of {
     TList t3 ->
      case enforce_type TInt t2 e2 of {
       Success e2' -> Success (ExistT (TList t3) (EBinop (TList t3) TInt
        (TList t3) (ORepeat t3) e1 e2'));
       Failure e -> Failure e};
     _ -> Failure (Dcons (unsafeCoerce e1) (Dcons (unsafeCoerce "has type")
      (Dcons (unsafeCoerce t1) (Dcons (unsafeCoerce "but expected") (Dcons
      (unsafeCoerce (\x -> TList x)) Dnil)))))};
   POPair -> Success (ExistT (TPair "0" t1 (TPair "1" t2 TEmpty)) (EBinop t1
    (TPair "1" t2 TEmpty) (TPair "0" t1 (TPair "1" t2 TEmpty)) (OPair "0" t1
    (TPair "1" t2 TEmpty)) e1 (EBinop t2 TEmpty (TPair "1" t2 TEmpty) (OPair
    "1" t2 TEmpty) e2 (EAtom TEmpty AEmpty))));
   POCons ->
    case enforce_type (TList t1) t2 e2 of {
     Success e2' -> Success (ExistT (TList t1) (EBinop t1 (TList t1) (TList
      t1) (OCons t1) e1 e2'));
     Failure e -> Failure e};
   PORange ->
    case enforce_type t1 t2 e2 of {
     Success e2' ->
      case t1 of {
       TWord -> Success (ExistT (TList TWord) (EBinop TWord TWord (TList
        TWord) OWRange e1 e2'));
       TInt -> Success (ExistT (TList TInt) (EBinop TInt TInt (TList TInt)
        ORange e1 e2'));
       _ -> Failure (Dcons (unsafeCoerce e1) (Dcons (unsafeCoerce "has type")
        (Dcons (unsafeCoerce t1) (Dcons (unsafeCoerce "but expected") (Dcons
        (unsafeCoerce TWord) (Dcons (unsafeCoerce "or") (Dcons
        (unsafeCoerce TInt) Dnil)))))))};
     Failure e -> Failure e}}

elaborate_proj :: Type -> Expr -> Prelude.String -> Result (SigT Type Expr)
elaborate_proj t0 e s =
  case t0 of {
   TPair s' t1 t2 ->
    case ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) s
           s' of {
     Prelude.True -> Success (ExistT t1 (EUnop (TPair s' t1 t2) t1 (OFst s'
      t1 t2) e));
     Prelude.False ->
      elaborate_proj t2 (EUnop (TPair s' t1 t2) t2 (OSnd s' t1 t2) e) s};
   TEmpty -> Failure (Dcons (unsafeCoerce "Field") (Dcons (unsafeCoerce s)
    (Dcons (unsafeCoerce "not found in record") Dnil)));
   _ -> Failure (Dcons (unsafeCoerce e) (Dcons (unsafeCoerce "has type")
    (Dcons (unsafeCoerce t0) (Dcons (unsafeCoerce "but expected") (Dcons
    (unsafeCoerce (\x x0 x1 -> TPair x x0 x1)) Dnil)))))}

elaborate_record :: (Map Prelude.String ((,) Type Prelude.Bool)) -> ((Rep
                    Prelude.String ((,) Type Prelude.Bool)) -> Pexpr ->
                    Result (SigT Type Expr)) -> (Rep Prelude.String
                    ((,) Type Prelude.Bool)) -> (([])
                    ((,) Prelude.String Pexpr)) -> Result (SigT Type Expr)
elaborate_record tenv0 elaborate0 g xs =
  case xs of {
   ([]) -> Success (ExistT TEmpty (EAtom TEmpty AEmpty));
   (:) p0 xs0 ->
    case p0 of {
     (,) s p ->
      case elaborate0 g p of {
       Success a ->
        case a of {
         ExistT x e1 ->
          case elaborate_record tenv0 elaborate0 g xs0 of {
           Success a0 ->
            case a0 of {
             ExistT x0 e2 -> Success (ExistT (TPair s x x0) (EBinop x x0
              (TPair s x x0) (OPair s x x0) e1 e2))};
           Failure e -> Failure e}};
       Failure e -> Failure e}}}

compute_wf :: (Map Prelude.String ((,) Type Prelude.Bool)) -> Type -> (Rep
              Prelude.String ((,) Type Prelude.Bool)) -> Expr -> Result 
              ()
compute_wf tenv0 _ g e =
  case e of {
   EVar t0 x ->
    case get tenv0 g x of {
     Prelude.Just p ->
      case p of {
       (,) t' b ->
        case b of {
         Prelude.True -> Failure (Dcons
          (unsafeCoerce "Expected EVar but got ELoc") (Dcons (unsafeCoerce x)
          Dnil));
         Prelude.False ->
          case type_eq_dec t0 t' of {
           Prelude.True -> Success ();
           Prelude.False -> Failure (Dcons (unsafeCoerce "Program has type")
            (Dcons (unsafeCoerce t0) (Dcons
            (unsafeCoerce "but environment has type") (Dcons
            (unsafeCoerce t') (Dcons (unsafeCoerce "for") (Dcons
            (unsafeCoerce x) Dnil))))))}}};
     Prelude.Nothing -> Failure (Dcons (unsafeCoerce "Undefined variable")
      (Dcons (unsafeCoerce x) Dnil))};
   ELoc t0 x ->
    case get tenv0 g x of {
     Prelude.Just p ->
      case p of {
       (,) t' b ->
        case b of {
         Prelude.True ->
          case type_eq_dec t0 t' of {
           Prelude.True -> Success ();
           Prelude.False -> Failure (Dcons (unsafeCoerce "Program has type")
            (Dcons (unsafeCoerce t0) (Dcons
            (unsafeCoerce "but environment has type") (Dcons
            (unsafeCoerce t') (Dcons (unsafeCoerce "for") (Dcons
            (unsafeCoerce x) Dnil))))))};
         Prelude.False -> Failure (Dcons
          (unsafeCoerce "Expected ELoc but got EVar") Dnil)}};
     Prelude.Nothing -> Failure (Dcons (unsafeCoerce "Undefined variable")
      (Dcons (unsafeCoerce x) Dnil))};
   EAtom _ _ -> Success ();
   EUnop t1 _ _ e0 -> compute_wf tenv0 t1 g e0;
   EBinop t1 t2 _ _ e1 e2 ->
    case compute_wf tenv0 t1 g e1 of {
     Success _ -> compute_wf tenv0 t2 g e2;
     Failure e0 -> Failure e0};
   EFlatmap t1 t2 e1 x e2 ->
    case compute_wf tenv0 (TList t1) g e1 of {
     Success _ ->
      let {g' = put tenv0 g x ((,) t1 Prelude.False)} in
      compute_wf tenv0 (TList t2) g' e2;
     Failure e0 -> Failure e0};
   EFold t1 t2 e1 e2 x y e3 ->
    case compute_wf tenv0 (TList t1) g e1 of {
     Success _ ->
      case compute_wf tenv0 t2 g e2 of {
       Success _ ->
        let {
         g' = put tenv0 (put tenv0 g x ((,) t1 Prelude.False)) y ((,) t2
                Prelude.False)}
        in
        compute_wf tenv0 t2 g' e3;
       Failure e0 -> Failure e0};
     Failure e0 -> Failure e0};
   EIf t0 e1 e2 e3 ->
    case compute_wf tenv0 TBool g e1 of {
     Success _ ->
      case compute_wf tenv0 t0 g e2 of {
       Success _ -> compute_wf tenv0 t0 g e3;
       Failure e0 -> Failure e0};
     Failure e0 -> Failure e0};
   ELet t1 t2 x e1 e2 ->
    case compute_wf tenv0 t1 g e1 of {
     Success _ ->
      let {g' = put tenv0 g x ((,) t1 Prelude.False)} in
      compute_wf tenv0 t2 g' e2;
     Failure e0 -> Failure e0}}

elaborate :: (Map Prelude.String ((,) Type Prelude.Bool)) -> (Rep
             Prelude.String ((,) Type Prelude.Bool)) -> Pexpr -> Result
             (SigT Type Expr)
elaborate tenv0 g p =
  case p of {
   PEVar x ->
    case get tenv0 g x of {
     Prelude.Just p0 ->
      case p0 of {
       (,) t0 b ->
        case b of {
         Prelude.True -> Success (ExistT t0 (ELoc t0 x));
         Prelude.False -> Success (ExistT t0 (EVar t0 x))}};
     Prelude.Nothing -> Failure (Dcons (unsafeCoerce "Undefined variable")
      (Dcons (unsafeCoerce x) Dnil))};
   PEAtom pa -> elaborate_atom pa;
   PESingleton p' ->
    case elaborate tenv0 g p' of {
     Success a ->
      case a of {
       ExistT t' e' -> Success (ExistT (TList t') (EBinop t' (TList t')
        (TList t') (OCons t') e' (EAtom (TList t') (ANil t'))))};
     Failure e -> Failure e};
   PEUnop po p0 ->
    case elaborate tenv0 g p0 of {
     Success a -> case a of {
                   ExistT t0 e -> elaborate_unop po t0 e};
     Failure e0 -> Failure e0};
   PEBinop po p1 p2 ->
    case elaborate tenv0 g p1 of {
     Success a ->
      case a of {
       ExistT t1 e1 ->
        case elaborate tenv0 g p2 of {
         Success a0 ->
          case a0 of {
           ExistT t2 e2 -> elaborate_binop po t1 t2 e1 e2};
         Failure e -> Failure e}};
     Failure e -> Failure e};
   PEFlatmap p1 x p2 ->
    case elaborate tenv0 g p1 of {
     Success a ->
      case a of {
       ExistT t1 e1 ->
        case t1 of {
         TList t2 ->
          let {g' = put tenv0 g x ((,) t2 Prelude.False)} in
          case elaborate tenv0 g' p2 of {
           Success a0 ->
            case a0 of {
             ExistT t3 e2 ->
              case t3 of {
               TList t4 -> Success (ExistT (TList t4) (EFlatmap t2 t4 e1 x
                e2));
               _ -> Failure (Dcons (unsafeCoerce e2) (Dcons
                (unsafeCoerce "has type") (Dcons (unsafeCoerce t3) (Dcons
                (unsafeCoerce "but expected") (Dcons
                (unsafeCoerce (\x0 -> TList x0)) Dnil)))))}};
           Failure e -> Failure e};
         _ -> Failure (Dcons (unsafeCoerce e1) (Dcons
          (unsafeCoerce "has type") (Dcons (unsafeCoerce t1) (Dcons
          (unsafeCoerce "but expected") (Dcons
          (unsafeCoerce (\x0 -> TList x0)) Dnil)))))}};
     Failure e -> Failure e};
   PEFold p1 p2 x y p3 ->
    case elaborate tenv0 g p1 of {
     Success a ->
      case a of {
       ExistT t1 e1 ->
        case t1 of {
         TList t2 ->
          case elaborate tenv0 g p2 of {
           Success a0 ->
            case a0 of {
             ExistT t3 e2 ->
              let {
               g' = put tenv0 (put tenv0 g x ((,) t2 Prelude.False)) y ((,)
                      t3 Prelude.False)}
              in
              case elaborate tenv0 g' p3 of {
               Success a1 ->
                case a1 of {
                 ExistT t4 e3 ->
                  case enforce_type t3 t4 e3 of {
                   Success e3' -> Success (ExistT t3 (EFold t2 t3 e1 e2 x y
                    e3'));
                   Failure e -> Failure e}};
               Failure e -> Failure e}};
           Failure e -> Failure e};
         _ -> Failure (Dcons (unsafeCoerce e1) (Dcons
          (unsafeCoerce "has type") (Dcons (unsafeCoerce t1) (Dcons
          (unsafeCoerce "but expected") (Dcons
          (unsafeCoerce (\x0 -> TList x0)) Dnil)))))}};
     Failure e -> Failure e};
   PEIf p1 p2 p3 ->
    case elaborate tenv0 g p1 of {
     Success a ->
      case a of {
       ExistT t1 e1 ->
        case elaborate tenv0 g p2 of {
         Success a0 ->
          case a0 of {
           ExistT t2 e2 ->
            case elaborate tenv0 g p3 of {
             Success a1 ->
              case a1 of {
               ExistT t3 e3 ->
                case enforce_type TBool t1 e1 of {
                 Success e1' ->
                  case enforce_type t2 t3 e3 of {
                   Success e3' -> Success (ExistT t2 (EIf t2 e1' e2 e3'));
                   Failure e -> Failure e};
                 Failure e -> Failure e}};
             Failure e -> Failure e}};
         Failure e -> Failure e}};
     Failure e -> Failure e};
   PELet x p1 p2 ->
    case elaborate tenv0 g p1 of {
     Success a ->
      case a of {
       ExistT t1 e1 ->
        let {g' = put tenv0 g x ((,) t1 Prelude.False)} in
        case elaborate tenv0 g' p2 of {
         Success a0 ->
          case a0 of {
           ExistT t2 e2 -> Success (ExistT t2 (ELet t1 t2 x e1 e2))};
         Failure e -> Failure e}};
     Failure e -> Failure e};
   PERecord ps -> elaborate_record tenv0 (elaborate tenv0) g ps;
   PEProj p0 s ->
    case elaborate tenv0 g p0 of {
     Success a -> case a of {
                   ExistT t0 e -> elaborate_proj t0 e s};
     Failure e0 -> Failure e0};
   PEElaborated t0 e ->
    case compute_wf tenv0 t0 g e of {
     Success _ -> Success (ExistT t0 e);
     Failure e0 -> Failure e0}}

elaborate_command :: (Map Prelude.String ((,) Type Prelude.Bool)) -> (Rep
                     Prelude.String ((,) Type Prelude.Bool)) -> Pcommand ->
                     Result Command
elaborate_command tenv0 g pc =
  case pc of {
   PCSkip -> Success CSkip;
   PCSeq pc1 pc2 ->
    case elaborate_command tenv0 g pc1 of {
     Success c1 ->
      case elaborate_command tenv0 g pc2 of {
       Success c2 -> Success (CSeq c1 c2);
       Failure e -> Failure e};
     Failure e -> Failure e};
   PCLet x p pc0 ->
    case elaborate tenv0 g p of {
     Success a ->
      case a of {
       ExistT t0 e ->
        case get tenv0 g x of {
         Prelude.Just p0 ->
          case p0 of {
           (,) _ b ->
            case b of {
             Prelude.True -> Failure (Dcons (unsafeCoerce "Variable") (Dcons
              (unsafeCoerce x) (Dcons
              (unsafeCoerce "already defined as mutable") Dnil)));
             Prelude.False ->
              let {g' = put tenv0 g x ((,) t0 Prelude.False)} in
              case elaborate_command tenv0 g' pc0 of {
               Success c -> Success (CLet t0 x e c);
               Failure e0 -> Failure e0}}};
         Prelude.Nothing ->
          let {g' = put tenv0 g x ((,) t0 Prelude.False)} in
          case elaborate_command tenv0 g' pc0 of {
           Success c -> Success (CLet t0 x e c);
           Failure e0 -> Failure e0}}};
     Failure e0 -> Failure e0};
   PCLetMut x p pc0 ->
    case elaborate tenv0 g p of {
     Success a ->
      case a of {
       ExistT t0 e ->
        case get tenv0 g x of {
         Prelude.Just p0 ->
          case p0 of {
           (,) _ b ->
            case b of {
             Prelude.True -> Failure (Dcons (unsafeCoerce "Mutable variable")
              (Dcons (unsafeCoerce x) (Dcons (unsafeCoerce "already defined")
              Dnil)));
             Prelude.False -> Failure (Dcons (unsafeCoerce "Variable") (Dcons
              (unsafeCoerce x) (Dcons
              (unsafeCoerce "already defined as immutable") Dnil)))}};
         Prelude.Nothing ->
          let {g' = put tenv0 g x ((,) t0 Prelude.True)} in
          case elaborate_command tenv0 g' pc0 of {
           Success c -> Success (CLetMut t0 x e c);
           Failure e0 -> Failure e0}}};
     Failure e0 -> Failure e0};
   PCGets x p ->
    case elaborate tenv0 g p of {
     Success a ->
      case a of {
       ExistT t0 e ->
        case get tenv0 g x of {
         Prelude.Just p0 ->
          case p0 of {
           (,) t' b ->
            case b of {
             Prelude.True ->
              case enforce_type t' t0 e of {
               Success e' -> Success (CGets t' x e');
               Failure e0 -> Failure e0};
             Prelude.False -> Failure (Dcons (unsafeCoerce "Variable") (Dcons
              (unsafeCoerce x) (Dcons (unsafeCoerce "is not mutable") Dnil)))}};
         Prelude.Nothing -> Failure (Dcons
          (unsafeCoerce "Undefined variable") (Dcons (unsafeCoerce x) Dnil))}};
     Failure e0 -> Failure e0};
   PCIf p pc1 pc2 ->
    case elaborate tenv0 g p of {
     Success a ->
      case a of {
       ExistT x e ->
        case enforce_type TBool x e of {
         Success e' ->
          case elaborate_command tenv0 g pc1 of {
           Success c1 ->
            case elaborate_command tenv0 g pc2 of {
             Success c2 -> Success (CIf e' c1 c2);
             Failure e0 -> Failure e0};
           Failure e0 -> Failure e0};
         Failure e0 -> Failure e0}};
     Failure e0 -> Failure e0};
   PCForeach x p pc0 ->
    case elaborate tenv0 g p of {
     Success a ->
      case a of {
       ExistT t0 e ->
        case t0 of {
         TList t1 ->
          let {g' = put tenv0 g x ((,) t1 Prelude.False)} in
          case elaborate_command tenv0 g' pc0 of {
           Success c -> Success (CForeach t1 x e c);
           Failure e0 -> Failure e0};
         _ -> Failure (Dcons (unsafeCoerce e) (Dcons
          (unsafeCoerce "has type") (Dcons (unsafeCoerce t0) (Dcons
          (unsafeCoerce "but expected") (Dcons
          (unsafeCoerce (\x0 -> TList x0)) Dnil)))))}};
     Failure e0 -> Failure e0}}

string_of_uint :: Uint -> Prelude.String
string_of_uint d =
  case d of {
   Nil -> "";
   D0 d0 -> (:) '0' (string_of_uint d0);
   D1 d0 -> (:) '1' (string_of_uint d0);
   D2 d0 -> (:) '2' (string_of_uint d0);
   D3 d0 -> (:) '3' (string_of_uint d0);
   D4 d0 -> (:) '4' (string_of_uint d0);
   D5 d0 -> (:) '5' (string_of_uint d0);
   D6 d0 -> (:) '6' (string_of_uint d0);
   D7 d0 -> (:) '7' (string_of_uint d0);
   D8 d0 -> (:) '8' (string_of_uint d0);
   D9 d0 -> (:) '9' (string_of_uint d0)}

string_of_uint0 :: Uint -> Prelude.String
string_of_uint0 d =
  case d of {
   Nil -> "0";
   _ -> string_of_uint d}

string_of_int :: Signed_int -> Prelude.String
string_of_int d =
  case d of {
   Pos d0 -> string_of_uint0 d0;
   Neg d0 -> (:) '-' (string_of_uint0 d0)}

type Interp_type = Any

default_val :: Prelude.Integer -> Word -> Type -> Interp_type
default_val width word0 t0 =
  case t0 of {
   TWord -> of_Z width word0 0;
   TInt -> unsafeCoerce 0;
   TBool -> unsafeCoerce Prelude.False;
   TString -> unsafeCoerce "";
   TPair _ t1 t2 ->
    unsafeCoerce ((,) (default_val width word0 t1)
      (default_val width word0 t2));
   TEmpty -> unsafeCoerce ();
   TList _ -> unsafeCoerce ([])}

eval_range :: Prelude.Integer -> Nat -> ([]) Prelude.Integer
eval_range lo len =
  case len of {
   O -> ([]);
   S n -> (:) lo (eval_range ((Prelude.+) lo ((\x -> x) 1)) n)}

eval_range_word :: Prelude.Integer -> Word -> Rep1 -> Nat -> ([]) Rep1
eval_range_word width word0 lo len =
  case len of {
   O -> ([]);
   S n -> (:) lo
    (eval_range_word width word0
      (add2 width word0 lo (of_Z width word0 ((\x -> x) 1))) n)}

proj_expected :: Prelude.Integer -> Word -> Type -> (SigT Type Interp_type)
                 -> Interp_type
proj_expected width word0 t_expected v =
  case type_eq_dec (projT1 v) t_expected of {
   Prelude.True -> cast (projT1 v) t_expected (projT2 v);
   Prelude.False -> default_val width word0 t_expected}

eqb_values :: Prelude.Integer -> Word -> Type -> Interp_type -> Interp_type
              -> Prelude.Bool
eqb_values width word0 t0 =
  case t0 of {
   TWord -> eqb3 width word0;
   TInt -> unsafeCoerce eqb1;
   TBool -> unsafeCoerce eqb;
   TString ->
    unsafeCoerce
      ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool);
   TEmpty -> (\_ _ -> Prelude.True);
   _ -> false_rect}

get_local :: Prelude.Integer -> Word -> (Map Prelude.String
             (SigT Type Interp_type)) -> (Rep Prelude.String
             (SigT Type Interp_type)) -> Type -> Prelude.String ->
             Interp_type
get_local width word0 locals0 l t0 x =
  case get locals0 l x of {
   Prelude.Just v -> proj_expected width word0 t0 v;
   Prelude.Nothing -> default_val width word0 t0}

set_local :: Prelude.Integer -> Word -> (Map Prelude.String
             (SigT Type Interp_type)) -> (Rep Prelude.String
             (SigT Type Interp_type)) -> Type -> Prelude.String ->
             Interp_type -> Rep Prelude.String (SigT Type Interp_type)
set_local _ _ locals0 l t0 x v =
  put locals0 l x (ExistT t0 v)

interp_atom :: Prelude.Integer -> Word -> Type -> Atom -> Interp_type
interp_atom width word0 _ a =
  case a of {
   AWord z -> of_Z width word0 z;
   AInt n -> unsafeCoerce n;
   ABool b -> unsafeCoerce b;
   AString s -> unsafeCoerce s;
   ANil _ -> unsafeCoerce ([]);
   AEmpty -> unsafeCoerce ()}

interp_unop :: Prelude.Integer -> Word -> Type -> Type -> Unop -> Interp_type
               -> Interp_type
interp_unop width word0 _ _ o =
  case o of {
   OWNeg -> opp0 width word0;
   ONeg -> unsafeCoerce opp;
   ONot -> unsafeCoerce Prelude.not;
   OLength _ -> (\x -> unsafeCoerce of_nat (length (unsafeCoerce x)));
   OLengthString -> (\x -> unsafeCoerce of_nat (length0 (unsafeCoerce x)));
   OFst _ _ _ -> unsafeCoerce fst;
   OSnd _ _ _ -> unsafeCoerce snd;
   OIntToString -> (\n ->
    unsafeCoerce string_of_int (to_int (unsafeCoerce n)))}

interp_binop :: Prelude.Integer -> Word -> Type -> Type -> Type -> Binop ->
                Interp_type -> Interp_type -> Interp_type
interp_binop width word0 _ _ _ o =
  case o of {
   OWPlus -> add2 width word0;
   OPlus -> unsafeCoerce (Prelude.+);
   OWMinus -> sub0 width word0;
   OMinus -> unsafeCoerce (Prelude.-);
   OWTimes -> mul1 width word0;
   OTimes -> unsafeCoerce (Prelude.*);
   OWDivU -> divu width word0;
   OWDivS -> divs width word0;
   ODiv -> unsafeCoerce div;
   OWModU -> modu width word0;
   OWModS -> mods width word0;
   OMod -> unsafeCoerce modulo;
   OAnd -> unsafeCoerce (Prelude.&&);
   OOr -> unsafeCoerce (Prelude.||);
   OConcat _ -> (\a b -> unsafeCoerce app a b);
   OConcatString -> unsafeCoerce append;
   OWLessU -> unsafeCoerce ltu width word0;
   OWLessS -> unsafeCoerce lts width word0;
   OLess -> unsafeCoerce ltb0;
   OEq t0 -> unsafeCoerce eqb_values width word0 t0;
   ORepeat _ -> (\l n ->
    unsafeCoerce concat (repeat (unsafeCoerce l) (to_nat0 (unsafeCoerce n))));
   OPair _ _ _ -> unsafeCoerce (\x x0 -> (,) x x0);
   OCons _ -> unsafeCoerce (\x x0 -> (:) x x0);
   ORange -> (\s e ->
    unsafeCoerce eval_range s
      (to_nat0 ((Prelude.-) (unsafeCoerce e) (unsafeCoerce s))));
   OWRange -> (\s e ->
    unsafeCoerce eval_range_word width word0 s
      (to_nat0
        ((Prelude.-) (unsigned width word0 e) (unsigned width word0 s))))}

interp_expr :: Prelude.Integer -> Word -> (Map Prelude.String
               (SigT Type Interp_type)) -> (Rep Prelude.String
               (SigT Type Interp_type)) -> Type -> Expr -> Interp_type
interp_expr width word0 locals0 l _ e =
  case e of {
   EVar t0 x -> get_local width word0 locals0 l t0 x;
   ELoc t0 x -> get_local width word0 locals0 l t0 x;
   EAtom t0 a -> interp_atom width word0 t0 a;
   EUnop t1 t2 o e1 ->
    interp_unop width word0 t1 t2 o (interp_expr width word0 locals0 l t1 e1);
   EBinop t1 t2 t3 o e1 e2 ->
    interp_binop width word0 t1 t2 t3 o
      (interp_expr width word0 locals0 l t1 e1)
      (interp_expr width word0 locals0 l t2 e2);
   EFlatmap t1 t2 l1 x fn ->
    unsafeCoerce flat_map (\y ->
      unsafeCoerce interp_expr width word0 locals0
        (set_local width word0 locals0 l t1 x y) (TList t2) fn)
      (unsafeCoerce interp_expr width word0 locals0 l (TList t1) l1);
   EFold t1 t2 l1 a x y fn ->
    let {l1' = interp_expr width word0 locals0 l (TList t1) l1} in
    let {a' = interp_expr width word0 locals0 l t2 a} in
    let {
     fn' = \v acc ->
      interp_expr width word0 locals0
        (set_local width word0 locals0
          (set_local width word0 locals0 l t1 x v) t2 y acc) t2 fn}
    in
    fold_right fn' a' (unsafeCoerce l1');
   EIf t0 e1 e2 e3 ->
    case unsafeCoerce interp_expr width word0 locals0 l TBool e1 of {
     Prelude.True -> interp_expr width word0 locals0 l t0 e2;
     Prelude.False -> interp_expr width word0 locals0 l t0 e3};
   ELet t1 t2 x e1 e2 ->
    interp_expr width word0 locals0
      (set_local width word0 locals0 l t1 x
        (interp_expr width word0 locals0 l t1 e1)) t2 e2}

interp_command :: Prelude.Integer -> Word -> (Map Prelude.String
                  (SigT Type Interp_type)) -> (Rep Prelude.String
                  (SigT Type Interp_type)) -> Command -> Rep Prelude.String
                  (SigT Type Interp_type)
interp_command width word0 locals0 l c =
  case c of {
   CSkip -> l;
   CSeq c1 c2 ->
    interp_command width word0 locals0
      (interp_command width word0 locals0 l c1) c2;
   CLet t0 x e c1 ->
    let {
     l' = interp_command width word0 locals0
            (set_local width word0 locals0 l t0 x
              (interp_expr width word0 locals0 l t0 e)) c1}
    in
    update locals0 l' x (get locals0 l x);
   CLetMut t0 x e c1 ->
    let {
     l' = interp_command width word0 locals0
            (set_local width word0 locals0 l t0 x
              (interp_expr width word0 locals0 l t0 e)) c1}
    in
    update locals0 l' x (get locals0 l x);
   CGets t0 x e ->
    set_local width word0 locals0 l t0 x
      (interp_expr width word0 locals0 l t0 e);
   CIf e c1 c2 ->
    case unsafeCoerce interp_expr width word0 locals0 l TBool e of {
     Prelude.True -> interp_command width word0 locals0 l c1;
     Prelude.False -> interp_command width word0 locals0 l c2};
   CForeach t0 x e c1 ->
    let {
     l' = fold_left (\l' v ->
            interp_command width word0 locals0
              (set_local width word0 locals0 l' t0 x v) c1)
            (unsafeCoerce interp_expr width word0 locals0 l (TList t0) e) l}
    in
    update locals0 l' x (get locals0 l x)}

generate_json_field_list_body :: (Type -> Expr -> Expr) -> (Type -> Expr ->
                                 Expr) -> Type -> Expr -> Expr
generate_json_field_list_body generate_json0 generate_json_field_list0 t0 var =
  case t0 of {
   TPair key t1 t2 ->
    case t2 of {
     TEmpty -> EBinop TString TString TString OConcatString (EBinop TString
      TString TString OConcatString (EBinop TString TString TString
      OConcatString (EAtom TString (AString key)) (EAtom TString (AString
      ": ")))
      (generate_json0 t1 (EUnop (TPair key t1 t2) t1 (OFst key t1 t2) var)))
      (EAtom TString (AString ""));
     _ -> EBinop TString TString TString OConcatString (EBinop TString
      TString TString OConcatString (EBinop TString TString TString
      OConcatString (EAtom TString (AString key)) (EAtom TString (AString
      ": ")))
      (generate_json0 t1 (EUnop (TPair key t1 t2) t1 (OFst key t1 t2) var)))
      (EBinop TString TString TString OConcatString (EAtom TString (AString
      ", "))
      (generate_json_field_list0 t2 (EUnop (TPair key t1 t2) t2 (OSnd key t1
        t2) var)))};
   TEmpty -> EAtom TString (AString "tt");
   _ -> EAtom TString (AString
    "Error this type cannot be conerted to a json object")}

generate_json :: Type -> Expr -> Expr
generate_json t0 var =
  case t0 of {
   TWord -> EAtom TString (AString "TODO");
   TInt -> EUnop TInt TString OIntToString var;
   TBool -> EIf TString (EBinop TBool TBool TBool (OEq TBool) var (EAtom
    TBool (ABool Prelude.True))) (EAtom TString (AString "true")) (EAtom
    TString (AString "false"));
   TString -> EBinop TString TString TString OConcatString (EBinop TString
    TString TString OConcatString (EAtom TString (AString "\"")) var) (EAtom
    TString (AString "\""));
   TPair key t1 t2 -> EBinop TString TString TString OConcatString (EBinop
    TString TString TString OConcatString (EAtom TString (AString "{"))
    (generate_json_field_list_body generate_json generate_json_field_list
      (TPair key t1 t2) var)) (EAtom TString (AString "}"));
   TEmpty -> EAtom TString (AString "tt");
   TList t1 -> EBinop TString TString TString OConcatString (EBinop TString
    TString TString OConcatString (EAtom TString (AString "[")) (EFold t1
    TString var (EAtom TString (AString "")) "v" "acc" (EBinop TString
    TString TString OConcatString (EBinop TString TString TString
    OConcatString (generate_json t1 (EVar t1 "v")) (EIf TString (EBinop
    TString TString TBool (OEq TString) (EVar TString "acc") (EAtom TString
    (AString ""))) (EAtom TString (AString "")) (EAtom TString (AString
    ", ")))) (EVar TString "acc")))) (EAtom TString (AString "]"))}

generate_json_field_list :: Type -> Expr -> Expr
generate_json_field_list t0 =
  generate_json_field_list_body generate_json generate_json_field_list t0

locals :: Prelude.Integer -> Word -> Map Prelude.String
          (SigT Type Interp_type)
locals _ _ =
  unsafeCoerce map1

tenv :: Map Prelude.String ((,) Type Prelude.Bool)
tenv =
  unsafeCoerce map1

init_locals :: Prelude.Integer -> Word -> (([]) ((,) Prelude.String Type)) ->
               Rep Prelude.String (SigT Type Interp_type)
init_locals width word0 vars =
  case vars of {
   ([]) -> empty (locals width word0);
   (:) p xs ->
    case p of {
     (,) x t0 ->
      set_local width word0 (locals width word0) (init_locals width word0 xs)
        t0 x (default_val width word0 t0)}}

map_to_locals :: Prelude.Integer -> Word -> (([])
                 ((,) Prelude.String ((,) Type Prelude.Bool))) -> Rep
                 Prelude.String (SigT Type Interp_type)
map_to_locals width word0 init =
  init_locals width word0
    (map (\x -> case x of {
                 (,) x0 y -> case y of {
                              (,) t0 _ -> (,) x0 t0}}) init)

run_program :: Prelude.Integer -> Word -> (([])
               ((,) Prelude.String ((,) Type Prelude.Bool))) -> Pcommand ->
               Result (([]) ((,) Key Value))
run_program width word0 init pc =
  case elaborate_command tenv (of_list tenv init) pc of {
   Success c -> Success
    (value build_parameters
      (unsafeCoerce interp_command width word0 (locals width word0)
        (map_to_locals width word0 init) c));
   Failure e -> Failure e}

type Rep2 = Prelude.Integer
  -- singleton inductive, whose constructor was mk
  
unsigned0 :: Prelude.Integer -> Rep2 -> Prelude.Integer
unsigned0 _ r =
  r

wrap :: Prelude.Integer -> Prelude.Integer -> Rep2
wrap width z =
  modulo z (pow ((\x -> x) ((\x -> 2 Prelude.* x) 1)) width)

signed :: Prelude.Integer -> Rep2 -> Prelude.Integer
signed width =
  let {
   wrap_value = \z ->
    modulo z (pow ((\x -> x) ((\x -> 2 Prelude.* x) 1)) width)}
  in
  let {
   swrap_value = \z ->
    (Prelude.-)
      (wrap_value
        ((Prelude.+) z
          (pow ((\x -> x) ((\x -> 2 Prelude.* x) 1))
            ((Prelude.-) width ((\x -> x) 1)))))
      (pow ((\x -> x) ((\x -> 2 Prelude.* x) 1))
        ((Prelude.-) width ((\x -> x) 1)))}
  in
  (\w -> swrap_value (unsigned0 width w))

data Special_cases =
   Build_special_cases (Prelude.Integer -> Prelude.Integer) (Prelude.Integer
                                                            ->
                                                            Prelude.Integer) 
 (Prelude.Integer -> Prelude.Integer)

div_by_zero :: Special_cases -> Prelude.Integer -> Prelude.Integer
div_by_zero s =
  case s of {
   Build_special_cases div_by_zero0 _ _ -> div_by_zero0}

mod_by_zero :: Special_cases -> Prelude.Integer -> Prelude.Integer
mod_by_zero s =
  case s of {
   Build_special_cases _ mod_by_zero0 _ -> mod_by_zero0}

adjust_too_big_shift_amount :: Special_cases -> Prelude.Integer ->
                               Prelude.Integer
adjust_too_big_shift_amount s =
  case s of {
   Build_special_cases _ _ adjust_too_big_shift_amount0 ->
    adjust_too_big_shift_amount0}

gen_word :: Prelude.Integer -> Special_cases -> Word
gen_word width sp =
  let {
   adjust_shift_amount = \n ->
    case ltb0 n width of {
     Prelude.True -> n;
     Prelude.False -> adjust_too_big_shift_amount sp n}}
  in
  Build_word (unsafeCoerce unsigned0 width) (unsafeCoerce signed width)
  (unsafeCoerce wrap width) (\x y ->
  unsafeCoerce wrap width
    ((Prelude.+) (unsigned0 width (unsafeCoerce x))
      (unsigned0 width (unsafeCoerce y)))) (\x y ->
  unsafeCoerce wrap width
    ((Prelude.-) (unsigned0 width (unsafeCoerce x))
      (unsigned0 width (unsafeCoerce y)))) (\x ->
  unsafeCoerce wrap width (opp (unsigned0 width (unsafeCoerce x)))) (\x y ->
  unsafeCoerce wrap width
    (lor1 (unsigned0 width (unsafeCoerce x))
      (unsigned0 width (unsafeCoerce y)))) (\x y ->
  unsafeCoerce wrap width
    (land1 (unsigned0 width (unsafeCoerce x))
      (unsigned0 width (unsafeCoerce y)))) (\x y ->
  unsafeCoerce wrap width
    (lxor1 (unsigned0 width (unsafeCoerce x))
      (unsigned0 width (unsafeCoerce y)))) (\x ->
  unsafeCoerce wrap width (lnot (unsigned0 width (unsafeCoerce x)))) (\x y ->
  unsafeCoerce wrap width
    (ldiff1 (unsigned0 width (unsafeCoerce x))
      (unsigned0 width (unsafeCoerce y)))) (\x y ->
  unsafeCoerce wrap width
    ((Prelude.*) (unsigned0 width (unsafeCoerce x))
      (unsigned0 width (unsafeCoerce y)))) (\x y ->
  unsafeCoerce wrap width
    (div
      ((Prelude.*) (signed width (unsafeCoerce x))
        (signed width (unsafeCoerce y)))
      (pow ((\x -> x) ((\x -> 2 Prelude.* x) 1)) width))) (\x y ->
  unsafeCoerce wrap width
    (div
      ((Prelude.*) (signed width (unsafeCoerce x))
        (unsigned0 width (unsafeCoerce y)))
      (pow ((\x -> x) ((\x -> 2 Prelude.* x) 1)) width))) (\x y ->
  unsafeCoerce wrap width
    (div
      ((Prelude.*) (unsigned0 width (unsafeCoerce x))
        (unsigned0 width (unsafeCoerce y)))
      (pow ((\x -> x) ((\x -> 2 Prelude.* x) 1)) width))) (\x y ->
  unsafeCoerce wrap width
    (case eqb1 (unsigned0 width (unsafeCoerce y)) 0 of {
      Prelude.True -> div_by_zero sp (unsigned0 width (unsafeCoerce x));
      Prelude.False ->
       div (unsigned0 width (unsafeCoerce x))
         (unsigned0 width (unsafeCoerce y))})) (\x y ->
  unsafeCoerce wrap width
    (case eqb1 (signed width (unsafeCoerce y)) 0 of {
      Prelude.True -> div_by_zero sp (signed width (unsafeCoerce x));
      Prelude.False ->
       quot (signed width (unsafeCoerce x)) (signed width (unsafeCoerce y))}))
  (\x y ->
  unsafeCoerce wrap width
    (case eqb1 (unsigned0 width (unsafeCoerce y)) 0 of {
      Prelude.True -> mod_by_zero sp (unsigned0 width (unsafeCoerce x));
      Prelude.False ->
       modulo (unsigned0 width (unsafeCoerce x))
         (unsigned0 width (unsafeCoerce y))})) (\x y ->
  unsafeCoerce wrap width
    (case eqb1 (signed width (unsafeCoerce y)) 0 of {
      Prelude.True -> mod_by_zero sp (signed width (unsafeCoerce x));
      Prelude.False ->
       rem (signed width (unsafeCoerce x)) (signed width (unsafeCoerce y))}))
  (\x y ->
  unsafeCoerce wrap width
    (shiftl (unsigned0 width (unsafeCoerce x))
      (adjust_shift_amount (unsigned0 width (unsafeCoerce y))))) (\x y ->
  unsafeCoerce wrap width
    (shiftr (unsigned0 width (unsafeCoerce x))
      (adjust_shift_amount (unsigned0 width (unsafeCoerce y))))) (\x y ->
  unsafeCoerce wrap width
    (shiftr (signed width (unsafeCoerce x))
      (adjust_shift_amount (unsigned0 width (unsafeCoerce y))))) (\x y ->
  eqb1 (unsigned0 width (unsafeCoerce x)) (unsigned0 width (unsafeCoerce y)))
  (\x y ->
  ltb0 (unsigned0 width (unsafeCoerce x)) (unsigned0 width (unsafeCoerce y)))
  (\x y ->
  ltb0 (signed width (unsafeCoerce x)) (signed width (unsafeCoerce y)))
  (\oldwidth z ->
  unsafeCoerce wrap width
    ((Prelude.-)
      (modulo
        ((Prelude.+) (unsigned0 width (unsafeCoerce z))
          (pow ((\x -> x) ((\x -> 2 Prelude.* x) 1))
            ((Prelude.-) oldwidth ((\x -> x) 1))))
        (pow ((\x -> x) ((\x -> 2 Prelude.* x) 1)) oldwidth))
      (pow ((\x -> x) ((\x -> 2 Prelude.* x) 1))
        ((Prelude.-) oldwidth ((\x -> x) 1)))))

default_special_case_handlers :: Prelude.Integer -> Special_cases
default_special_case_handlers width =
  Build_special_cases (\_ -> Prelude.negate 1) (\x -> x) (\n ->
    modulo n (pow ((\x -> x) ((\x -> 2 Prelude.* x) 1)) (log2 width)))

word :: Prelude.Integer -> Word
word width =
  gen_word width (default_special_case_handlers width)

record :: (([]) ((,) Prelude.String Type)) -> Type
record l =
  case l of {
   ([]) -> TEmpty;
   (:) p xs -> case p of {
                (,) s t0 -> TPair s t0 (record xs)}}

artist :: Type
artist =
  record ((:) ((,) "id" TInt) ((:) ((,) "name" TString) ([])))

pexpr_list :: Type -> (([]) Pexpr) -> Pexpr
pexpr_list t0 l =
  case l of {
   ([]) -> PEAtom (PANil t0);
   (:) x xs -> PEBinop POCons x (pexpr_list t0 xs)}

as_pexpr :: Prelude.Integer -> Word -> Type -> Interp_type -> Pexpr
as_pexpr width word0 t0 v =
  case t0 of {
   TWord -> PEAtom (PAWord (unsigned width word0 v));
   TInt -> PEAtom (PAInt (unsafeCoerce v));
   TBool -> PEAtom (PABool (unsafeCoerce v));
   TString -> PEAtom (PAString (unsafeCoerce v));
   TPair _ t1 t2 -> PEBinop POPair
    (as_pexpr width word0 t1 (fst (unsafeCoerce v)))
    (as_pexpr width word0 t2 (snd (unsafeCoerce v)));
   TEmpty -> PERecord ([]);
   TList t1 -> pexpr_list t1 (map (as_pexpr width word0 t1) (unsafeCoerce v))}

zip :: (([]) a1) -> (([]) a2) -> ([]) ((,) a1 a2)
zip l1 l2 =
  case l1 of {
   ([]) -> ([]);
   (:) x xs ->
    case l2 of {
     ([]) -> ([]);
     (:) y ys -> (:) ((,) x y) (zip xs ys)}}

pexperify :: Prelude.Integer -> Word -> (([]) ((,) Prelude.String Type)) ->
             Interp_type -> ([]) Pexpr
pexperify width word0 l tp =
  case l of {
   ([]) -> ([]);
   (:) p xs ->
    case p of {
     (,) _ t0 -> (:) (as_pexpr width word0 t0 (fst (unsafeCoerce tp)))
      (pexperify width word0 xs (snd (unsafeCoerce tp)))}}

from_tuple' :: Prelude.Integer -> Word -> (([]) ((,) Prelude.String Type)) ->
               Interp_type -> Pexpr
from_tuple' width word0 l tp =
  PERecord (zip (map fst l) (pexperify width word0 l tp))

artist_1' :: Prelude.Integer -> Word -> Pexpr
artist_1' width word0 =
  from_tuple' width word0 ((:) ((,) "id" TInt) ((:) ((,) "name" TString)
    ([]))) (unsafeCoerce ((,) ((\x -> x) 1) ((,) "AC/DC" ())))

artist_2' :: Prelude.Integer -> Word -> Pexpr
artist_2' width word0 =
  from_tuple' width word0 ((:) ((,) "id" TInt) ((:) ((,) "name" TString)
    ([])))
    (unsafeCoerce ((,) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) ((,) "Accept"
      ())))

artist_3' :: Prelude.Integer -> Word -> Pexpr
artist_3' width word0 =
  from_tuple' width word0 ((:) ((,) "id" TInt) ((:) ((,) "name" TString)
    ([])))
    (unsafeCoerce ((,) ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1)) ((,)
      "Aerosmith" ())))

artist_4' :: Prelude.Integer -> Word -> Pexpr
artist_4' width word0 =
  from_tuple' width word0 ((:) ((,) "id" TInt) ((:) ((,) "name" TString)
    ([])))
    (unsafeCoerce ((,) ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1))) ((,) "Alanis Morisette" ())))

artists' :: Prelude.Integer -> Word -> Pexpr
artists' width word0 =
  pexpr_list artist ((:) (artist_1' width word0) ((:) (artist_2' width word0)
    ((:) (artist_3' width word0) ((:) (artist_4' width word0) ([])))))

filter_test :: Prelude.Integer -> Word -> Prelude.Integer -> Pcommand
filter_test width word0 n =
  PCSeq (PCGets "ans" (PEFlatmap (artists' width word0) "x" (PEIf (PEBinop
    POLess (PEProj (PEVar "x") "id") (PEAtom (PAInt n))) (PESingleton (PEVar
    "x")) (PEAtom (PANil artist))))) (PCGets "json" (PEElaborated TString
    (generate_json (TList artist) (ELoc (TList artist) "ans"))))

album :: Type
album =
  record ((:) ((,) "album_id" TInt) ((:) ((,) "title" TString) ((:) ((,)
    "artist_id" TInt) ([]))))

albums :: Prelude.Integer -> Word -> Pexpr
albums width word0 =
  pexpr_list album
    (map
      (unsafeCoerce from_tuple' width word0 ((:) ((,) "album_id" TInt) ((:)
        ((,) "title" TString) ((:) ((,) "artist_id" TInt) ([]))))) ((:) ((,)
      ((\x -> x) 1) ((,) "For Those About To Rock We Salute You" ((,)
      ((\x -> x) 1) ()))) ((:) ((,) ((\x -> x) ((\x -> 2 Prelude.* x) 1))
      ((,) "Balls to the Wall" ((,) ((\x -> x) ((\x -> 2 Prelude.* x) 1))
      ()))) ((:) ((,) ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1)) ((,)
      "Restless and Wild" ((,) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) ())))
      ((:) ((,) ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))
      ((,) "Let There Be Rock" ((,) ((\x -> x) 1) ()))) ((:) ((,) ((\x -> x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) 1))) ((,)
      "Big Ones" ((,) ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1)) ())))
      ((:) ((,) ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))) ((,) "Jaggged Little Pill" ((,)
      ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1))) ())))
      ((:) ((,) ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
      ((\x -> 2 Prelude.* x Prelude.+ 1) 1))) ((,) "Facelift" ((,) ((\x -> x)
      ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) 1))) ())))
      ([])))))))))

t :: Type
t =
  TPair "0" album (TPair "1" artist TEmpty)

filter_albums_with_artist :: Prelude.Integer -> Word -> Pexpr -> Pcommand
filter_albums_with_artist width word0 n =
  PCSeq (PCGets "ans" (PEFlatmap (PEFlatmap (albums width word0) "y"
    (PEFlatmap (artists' width word0) "z" (PESingleton (PEBinop POPair (PEVar
    "y") (PEVar "z"))))) "x" (PEIf (PEBinop POAnd (PEBinop POEq (PEProj
    (PEProj (PEVar "x") "0") "artist_id") (PEProj (PEProj (PEVar "x") "1")
    "id")) (PEBinop POEq (PEProj (PEProj (PEVar "x") "0") "album_id") n))
    (PESingleton (PEVar "x")) (PEAtom (PANil t))))) (PCGets "json"
    (PEElaborated TString
    (generate_json (TList
      (record ((:) ((,) "0" album) ((:) ((,) "1" artist) ([]))))) (ELoc
      (TList (record ((:) ((,) "0" album) ((:) ((,) "1" artist) ([])))))
      "ans"))))

export_prog :: (([]) ((,) Prelude.String ((,) Type Prelude.Bool))) ->
               Pcommand -> Prelude.String
export_prog l p =
  let {
   output = run_program ((\x -> x) ((\x -> 2 Prelude.* x)
              ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
              ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
              ((\x -> 2 Prelude.* x) 1)))))))
              (word ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
                ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
                ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))))))) l p}
  in
  let {
   getJsonStrs = flat_map (\p0 ->
                   case p0 of {
                    (,) y y0 ->
                     case y of {
                      ([]) -> ([]);
                      (:) a s0 ->
                       (\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0)
              (Data.Bits.testBit (Data.Char.ord a) 1)
              (Data.Bits.testBit (Data.Char.ord a) 2)
              (Data.Bits.testBit (Data.Char.ord a) 3)
              (Data.Bits.testBit (Data.Char.ord a) 4)
              (Data.Bits.testBit (Data.Char.ord a) 5)
              (Data.Bits.testBit (Data.Char.ord a) 6)
              (Data.Bits.testBit (Data.Char.ord a) 7))
                         (\b b0 b1 b2 b3 b4 b5 b6 ->
                         case b of {
                          Prelude.True -> ([]);
                          Prelude.False ->
                           case b0 of {
                            Prelude.True ->
                             case b1 of {
                              Prelude.True -> ([]);
                              Prelude.False ->
                               case b2 of {
                                Prelude.True ->
                                 case b3 of {
                                  Prelude.True -> ([]);
                                  Prelude.False ->
                                   case b4 of {
                                    Prelude.True ->
                                     case b5 of {
                                      Prelude.True ->
                                       case b6 of {
                                        Prelude.True -> ([]);
                                        Prelude.False ->
                                         case s0 of {
                                          ([]) -> ([]);
                                          (:) a0 s1 ->
                                           (\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0)
              (Data.Bits.testBit (Data.Char.ord a) 1)
              (Data.Bits.testBit (Data.Char.ord a) 2)
              (Data.Bits.testBit (Data.Char.ord a) 3)
              (Data.Bits.testBit (Data.Char.ord a) 4)
              (Data.Bits.testBit (Data.Char.ord a) 5)
              (Data.Bits.testBit (Data.Char.ord a) 6)
              (Data.Bits.testBit (Data.Char.ord a) 7))
                                             (\b7 b8 b9 b10 b11 b12 b13 b14 ->
                                             case b7 of {
                                              Prelude.True ->
                                               case b8 of {
                                                Prelude.True ->
                                                 case b9 of {
                                                  Prelude.True -> ([]);
                                                  Prelude.False ->
                                                   case b10 of {
                                                    Prelude.True -> ([]);
                                                    Prelude.False ->
                                                     case b11 of {
                                                      Prelude.True ->
                                                       case b12 of {
                                                        Prelude.True ->
                                                         case b13 of {
                                                          Prelude.True ->
                                                           case b14 of {
                                                            Prelude.True ->
                                                             ([]);
                                                            Prelude.False ->
                                                             case s1 of {
                                                              ([]) -> ([]);
                                                              (:) a1 s2 ->
                                                               (\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0)
              (Data.Bits.testBit (Data.Char.ord a) 1)
              (Data.Bits.testBit (Data.Char.ord a) 2)
              (Data.Bits.testBit (Data.Char.ord a) 3)
              (Data.Bits.testBit (Data.Char.ord a) 4)
              (Data.Bits.testBit (Data.Char.ord a) 5)
              (Data.Bits.testBit (Data.Char.ord a) 6)
              (Data.Bits.testBit (Data.Char.ord a) 7))
                                                                 (\b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                 case b15 of {
                                                                  Prelude.True ->
                                                                   case b16 of {
                                                                    Prelude.True ->
                                                                    case b17 of {
                                                                     Prelude.True ->
                                                                    case b18 of {
                                                                     Prelude.True ->
                                                                    case b19 of {
                                                                     Prelude.True ->
                                                                    ([]);
                                                                     Prelude.False ->
                                                                    case b20 of {
                                                                     Prelude.True ->
                                                                    case b21 of {
                                                                     Prelude.True ->
                                                                    case b22 of {
                                                                     Prelude.True ->
                                                                    ([]);
                                                                     Prelude.False ->
                                                                    case s2 of {
                                                                     ([]) ->
                                                                    ([]);
                                                                     (:) a2
                                                                    s3 ->
                                                                    (\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0)
              (Data.Bits.testBit (Data.Char.ord a) 1)
              (Data.Bits.testBit (Data.Char.ord a) 2)
              (Data.Bits.testBit (Data.Char.ord a) 3)
              (Data.Bits.testBit (Data.Char.ord a) 4)
              (Data.Bits.testBit (Data.Char.ord a) 5)
              (Data.Bits.testBit (Data.Char.ord a) 6)
              (Data.Bits.testBit (Data.Char.ord a) 7))
                                                                    (\b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    case b23 of {
                                                                     Prelude.True ->
                                                                    ([]);
                                                                     Prelude.False ->
                                                                    case b24 of {
                                                                     Prelude.True ->
                                                                    case b25 of {
                                                                     Prelude.True ->
                                                                    case b26 of {
                                                                     Prelude.True ->
                                                                    case b27 of {
                                                                     Prelude.True ->
                                                                    ([]);
                                                                     Prelude.False ->
                                                                    case b28 of {
                                                                     Prelude.True ->
                                                                    case b29 of {
                                                                     Prelude.True ->
                                                                    case b30 of {
                                                                     Prelude.True ->
                                                                    ([]);
                                                                     Prelude.False ->
                                                                    case s3 of {
                                                                     ([]) ->
                                                                    case y0 of {
                                                                     ExistT x
                                                                    s ->
                                                                    case x of {
                                                                     TWord ->
                                                                    ([]);
                                                                     TInt ->
                                                                    ([]);
                                                                     TBool ->
                                                                    ([]);
                                                                     TString ->
                                                                    (:) s
                                                                    ([]);
                                                                     TPair _
                                                                    _ _ ->
                                                                    ([]);
                                                                     TEmpty ->
                                                                    ([]);
                                                                     TList _ ->
                                                                    ([])}};
                                                                     (:) _
                                                                    _ -> ([])}};
                                                                     Prelude.False ->
                                                                    ([])};
                                                                     Prelude.False ->
                                                                    ([])}};
                                                                     Prelude.False ->
                                                                    ([])};
                                                                     Prelude.False ->
                                                                    ([])};
                                                                     Prelude.False ->
                                                                    ([])}})
                                                                    a2}};
                                                                     Prelude.False ->
                                                                    ([])};
                                                                     Prelude.False ->
                                                                    ([])}};
                                                                     Prelude.False ->
                                                                    ([])};
                                                                     Prelude.False ->
                                                                    ([])};
                                                                    Prelude.False ->
                                                                    ([])};
                                                                  Prelude.False ->
                                                                   ([])})
                                                                 a1}};
                                                          Prelude.False ->
                                                           ([])};
                                                        Prelude.False -> ([])};
                                                      Prelude.False -> ([])}}};
                                                Prelude.False -> ([])};
                                              Prelude.False -> ([])})
                                             a0}};
                                      Prelude.False -> ([])};
                                    Prelude.False -> ([])}};
                                Prelude.False -> ([])}};
                            Prelude.False -> ([])}})
                         a}})}
  in
  case output of {
   Success locals0 ->
    case unsafeCoerce getJsonStrs locals0 of {
     ([]) -> "Error: Program did not output json str";
     (:) str l0 ->
      case l0 of {
       ([]) -> str;
       (:) _ _ -> "Error: Program did not output json str"}};
   Failure _ -> "Error: Program errored"}

exported_get_artist :: Prelude.Integer -> Prelude.String
exported_get_artist n =
  export_prog ((:) ((,) "json" ((,) TString Prelude.True)) ((:) ((,) "ans"
    ((,) (TList artist) Prelude.True)) ([])))
    (filter_test ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) 1)))))))
      (word ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
        ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
        ((\x -> 2 Prelude.* x) 1)))))))) n)

exported_get_album_and_artist :: Prelude.Integer -> Prelude.String
exported_get_album_and_artist n =
  export_prog ((:) ((,) "json" ((,) TString Prelude.True)) ((:) ((,) "ans"
    ((,) (TList (record ((:) ((,) "0" album) ((:) ((,) "1" artist) ([])))))
    Prelude.True)) ([])))
    (filter_albums_with_artist ((\x -> x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))))))
      (word ((\x -> x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
        ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
        ((\x -> 2 Prelude.* x) 1)))))))) (PEAtom (PAInt n)))

exported :: (,) (Prelude.Integer -> Prelude.String)
            (Prelude.Integer -> Prelude.String)
exported =
  (,) exported_get_artist exported_get_album_and_artist

