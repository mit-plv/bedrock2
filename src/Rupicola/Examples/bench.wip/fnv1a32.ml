
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

type comparison =
| Eq
| Lt
| Gt

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)let rec add n m =
   match n with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

type byte =
| X00
| X01
| X02
| X03
| X04
| X05
| X06
| X07
| X08
| X09
| X0a
| X0b
| X0c
| X0d
| X0e
| X0f
| X10
| X11
| X12
| X13
| X14
| X15
| X16
| X17
| X18
| X19
| X1a
| X1b
| X1c
| X1d
| X1e
| X1f
| X20
| X21
| X22
| X23
| X24
| X25
| X26
| X27
| X28
| X29
| X2a
| X2b
| X2c
| X2d
| X2e
| X2f
| X30
| X31
| X32
| X33
| X34
| X35
| X36
| X37
| X38
| X39
| X3a
| X3b
| X3c
| X3d
| X3e
| X3f
| X40
| X41
| X42
| X43
| X44
| X45
| X46
| X47
| X48
| X49
| X4a
| X4b
| X4c
| X4d
| X4e
| X4f
| X50
| X51
| X52
| X53
| X54
| X55
| X56
| X57
| X58
| X59
| X5a
| X5b
| X5c
| X5d
| X5e
| X5f
| X60
| X61
| X62
| X63
| X64
| X65
| X66
| X67
| X68
| X69
| X6a
| X6b
| X6c
| X6d
| X6e
| X6f
| X70
| X71
| X72
| X73
| X74
| X75
| X76
| X77
| X78
| X79
| X7a
| X7b
| X7c
| X7d
| X7e
| X7f
| X80
| X81
| X82
| X83
| X84
| X85
| X86
| X87
| X88
| X89
| X8a
| X8b
| X8c
| X8d
| X8e
| X8f
| X90
| X91
| X92
| X93
| X94
| X95
| X96
| X97
| X98
| X99
| X9a
| X9b
| X9c
| X9d
| X9e
| X9f
| Xa0
| Xa1
| Xa2
| Xa3
| Xa4
| Xa5
| Xa6
| Xa7
| Xa8
| Xa9
| Xaa
| Xab
| Xac
| Xad
| Xae
| Xaf
| Xb0
| Xb1
| Xb2
| Xb3
| Xb4
| Xb5
| Xb6
| Xb7
| Xb8
| Xb9
| Xba
| Xbb
| Xbc
| Xbd
| Xbe
| Xbf
| Xc0
| Xc1
| Xc2
| Xc3
| Xc4
| Xc5
| Xc6
| Xc7
| Xc8
| Xc9
| Xca
| Xcb
| Xcc
| Xcd
| Xce
| Xcf
| Xd0
| Xd1
| Xd2
| Xd3
| Xd4
| Xd5
| Xd6
| Xd7
| Xd8
| Xd9
| Xda
| Xdb
| Xdc
| Xdd
| Xde
| Xdf
| Xe0
| Xe1
| Xe2
| Xe3
| Xe4
| Xe5
| Xe6
| Xe7
| Xe8
| Xe9
| Xea
| Xeb
| Xec
| Xed
| Xee
| Xef
| Xf0
| Xf1
| Xf2
| Xf3
| Xf4
| Xf5
| Xf6
| Xf7
| Xf8
| Xf9
| Xfa
| Xfb
| Xfc
| Xfd
| Xfe
| Xff

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  if b1 then b2 else if b2 then false else true

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of int
  | IsNeg
 end

module Coq_Pos =
 struct
  (** val succ : int -> int **)

  let rec succ = Pervasives.succ

  (** val add : int -> int -> int **)

  let rec add = (+)

  (** val add_carry : int -> int -> int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add_carry p q))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun _ -> (fun p->1+2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (succ q))
        (fun q -> (fun p->2*p) (succ q))
        (fun _ -> (fun p->1+2*p) 1)
        y)
      x

  (** val pred_double : int -> int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->1+2*p) ((fun p->2*p) p))
      (fun p -> (fun p->1+2*p) (pred_double p))
      (fun _ -> 1)
      x

  (** val pred_N : int -> int **)

  let pred_N x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> ((fun p->2*p) p))
      (fun p -> (pred_double p))
      (fun _ -> 0)
      x

  type mask = Pos.mask =
  | IsNul
  | IsPos of int
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos 1
  | IsPos p -> IsPos ((fun p->1+2*p) p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos ((fun p->2*p) p)
  | x0 -> x0

  (** val double_pred_mask : int -> mask **)

  let double_pred_mask x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> IsPos ((fun p->2*p) ((fun p->2*p) p)))
      (fun p -> IsPos ((fun p->2*p) (pred_double p)))
      (fun _ -> IsNul)
      x

  (** val sub_mask : int -> int -> mask **)

  let rec sub_mask x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double_mask (sub_mask p q))
        (fun q -> succ_double_mask (sub_mask p q))
        (fun _ -> IsPos ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> succ_double_mask (sub_mask_carry p q))
        (fun q -> double_mask (sub_mask p q))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> IsNeg)
        (fun _ -> IsNeg)
        (fun _ -> IsNul)
        y)
      x

  (** val sub_mask_carry : int -> int -> mask **)

  and sub_mask_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> succ_double_mask (sub_mask_carry p q))
        (fun q -> double_mask (sub_mask p q))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double_mask (sub_mask_carry p q))
        (fun q -> succ_double_mask (sub_mask_carry p q))
        (fun _ -> double_pred_mask p)
        y)
      (fun _ -> IsNeg)
      x

  (** val mul : int -> int -> int **)

  let rec mul = ( * )

  (** val iter : ('a1 -> 'a1) -> 'a1 -> int -> 'a1 **)

  let rec iter f x n =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun n' -> f (iter f (iter f x n') n'))
      (fun n' -> iter f (iter f x n') n')
      (fun _ -> f x)
      n

  (** val div2 : int -> int **)

  let div2 p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> p0)
      (fun p0 -> p0)
      (fun _ -> 1)
      p

  (** val div2_up : int -> int **)

  let div2_up p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> succ p0)
      (fun p0 -> p0)
      (fun _ -> 1)
      p

  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont = fun c x y -> if x=y then c else if x<y then Lt else Gt

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val eqb : int -> int -> bool **)

  let rec eqb p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        (fun _ -> false)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        q)
      p

  (** val coq_Nsucc_double : int -> int **)

  let coq_Nsucc_double x =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      x

  (** val coq_Ndouble : int -> int **)

  let coq_Ndouble n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      n

  (** val coq_lor : int -> int -> int **)

  let rec coq_lor p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p) (coq_lor p0 q0))
        (fun q0 -> (fun p->1+2*p) (coq_lor p0 q0))
        (fun _ -> p)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p) (coq_lor p0 q0))
        (fun q0 -> (fun p->2*p) (coq_lor p0 q0))
        (fun _ -> (fun p->1+2*p) p0)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> q)
        (fun q0 -> (fun p->1+2*p) q0)
        (fun _ -> q)
        q)
      p

  (** val coq_land : int -> int -> int **)

  let rec coq_land p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Nsucc_double (coq_land p0 q0))
        (fun q0 -> coq_Ndouble (coq_land p0 q0))
        (fun _ -> 1)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (coq_land p0 q0))
        (fun q0 -> coq_Ndouble (coq_land p0 q0))
        (fun _ -> 0)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> 1)
        (fun _ -> 0)
        (fun _ -> 1)
        q)
      p

  (** val ldiff : int -> int -> int **)

  let rec ldiff p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (ldiff p0 q0))
        (fun q0 -> coq_Nsucc_double (ldiff p0 q0))
        (fun _ -> ((fun p->2*p) p0))
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (ldiff p0 q0))
        (fun q0 -> coq_Ndouble (ldiff p0 q0))
        (fun _ -> p)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> 0)
        (fun _ -> 1)
        (fun _ -> 0)
        q)
      p

  (** val coq_lxor : int -> int -> int **)

  let rec coq_lxor p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (coq_lxor p0 q0))
        (fun q0 -> coq_Nsucc_double (coq_lxor p0 q0))
        (fun _ -> ((fun p->2*p) p0))
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Nsucc_double (coq_lxor p0 q0))
        (fun q0 -> coq_Ndouble (coq_lxor p0 q0))
        (fun _ -> ((fun p->1+2*p) p0))
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> ((fun p->2*p) q0))
        (fun q0 -> ((fun p->1+2*p) q0))
        (fun _ -> 0)
        q)
      p

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> op a (iter_op op p0 (op a a)))
      (fun p0 -> iter_op op p0 (op a a))
      (fun _ -> a)
      p

  (** val to_nat : int -> nat **)

  let to_nat x =
    iter_op Coq__1.add x (S O)

  (** val of_succ_nat : nat -> int **)

  let rec of_succ_nat = function
  | O -> 1
  | S x -> succ (of_succ_nat x)
 end

module N =
 struct
  (** val compare : int -> int -> comparison **)

  let compare n m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> (fun f0 fp n -> if n=0 then f0 () else fp n)
                  (fun _ -> Eq)
                  (fun _ -> Lt)
                  m)
      (fun n' -> (fun f0 fp n -> if n=0 then f0 () else fp n)
                   (fun _ -> Gt)
                   (fun m' -> Coq_Pos.compare n' m')
                   m)
      n

  (** val ltb : int -> int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false
 end

module Coq_N =
 struct
  (** val succ_double : int -> int **)

  let succ_double x =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      x

  (** val double : int -> int **)

  let double n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      n

  (** val succ_pos : int -> int **)

  let succ_pos n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 1)
      (fun p -> Coq_Pos.succ p)
      n

  (** val add : int -> int -> int **)

  let add = (+)

  (** val sub : int -> int -> int **)

  let sub = fun n m -> Pervasives.max 0 (n-m)

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val leb : int -> int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val pos_div_eucl : int -> int -> int * int **)

  let rec pos_div_eucl a b =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in let r' = succ_double r in if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r'))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in let r' = double r in if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r'))
      (fun _ ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> (0, 1))
        (fun p ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun _ -> (0, 1))
          (fun _ -> (0, 1))
          (fun _ -> (1, 0))
          p)
        b)
      a

  (** val coq_lor : int -> int -> int **)

  let coq_lor n m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> m)
      (fun p -> (fun f0 fp n -> if n=0 then f0 () else fp n)
                  (fun _ -> n)
                  (fun q -> (Coq_Pos.coq_lor p q))
                  m)
      n

  (** val coq_land : int -> int -> int **)

  let coq_land n m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> (fun f0 fp n -> if n=0 then f0 () else fp n)
                  (fun _ -> 0)
                  (fun q -> Coq_Pos.coq_land p q)
                  m)
      n

  (** val ldiff : int -> int -> int **)

  let rec ldiff n m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> (fun f0 fp n -> if n=0 then f0 () else fp n)
                  (fun _ -> n)
                  (fun q -> Coq_Pos.ldiff p q)
                  m)
      n

  (** val coq_lxor : int -> int -> int **)

  let coq_lxor n m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> m)
      (fun p -> (fun f0 fp n -> if n=0 then f0 () else fp n)
                  (fun _ -> n)
                  (fun q -> Coq_Pos.coq_lxor p q)
                  m)
      n
 end

(** val nth : nat -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n l default0 =
  match n with
  | O -> (match l with
          | [] -> default0
          | x :: _ -> x)
  | S m -> (match l with
            | [] -> default0
            | _ :: t0 -> nth m t0 default0)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: t0 -> f b (fold_right f a0 t0)

(** val find : ('a1 -> bool) -> 'a1 list -> 'a1 option **)

let rec find f = function
| [] -> None
| x :: tl -> if f x then Some x else find f tl

module Z =
 struct
  (** val to_nat : int -> nat **)

  let to_nat z =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> O)
      (fun p -> Coq_Pos.to_nat p)
      (fun _ -> O)
      z
 end

module Coq_Z =
 struct
  (** val double : int -> int **)

  let double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      (fun p -> (~-) ((fun p->2*p) p))
      x

  (** val succ_double : int -> int **)

  let succ_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      (fun p -> (~-) (Coq_Pos.pred_double p))
      x

  (** val pred_double : int -> int **)

  let pred_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (~-) 1)
      (fun p -> (Coq_Pos.pred_double p))
      (fun p -> (~-) ((fun p->1+2*p) p))
      x

  (** val pos_sub : int -> int -> int **)

  let rec pos_sub x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double (pos_sub p q))
        (fun q -> succ_double (pos_sub p q))
        (fun _ -> ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> pred_double (pos_sub p q))
        (fun q -> double (pos_sub p q))
        (fun _ -> (Coq_Pos.pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (~-) ((fun p->2*p) q))
        (fun q -> (~-) (Coq_Pos.pred_double q))
        (fun _ -> 0)
        y)
      x

  (** val add : int -> int -> int **)

  let add = (+)

  (** val opp : int -> int **)

  let opp = (~-)

  (** val pred : int -> int **)

  let pred = Pervasives.pred

  (** val sub : int -> int -> int **)

  let sub = (-)

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val pow_pos : int -> int -> int **)

  let pow_pos z =
    Coq_Pos.iter (mul z) 1

  (** val pow : int -> int -> int **)

  let pow x y =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p -> pow_pos x p)
      (fun _ -> 0)
      y

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val leb : int -> int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : int -> int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val eqb : int -> int -> bool **)

  let rec eqb x y =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun q -> Coq_Pos.eqb p q)
        (fun _ -> false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun _ -> false)
        (fun q -> Coq_Pos.eqb p q)
        y)
      x

  (** val max : int -> int -> int **)

  let max = Pervasives.max

  (** val to_nat : int -> nat **)

  let to_nat z =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> O)
      (fun p -> Coq_Pos.to_nat p)
      (fun _ -> O)
      z

  (** val of_nat : nat -> int **)

  let of_nat = function
  | O -> 0
  | S n0 -> (Coq_Pos.of_succ_nat n0)

  (** val of_N : int -> int **)

  let of_N = fun p -> p

  (** val pos_div_eucl : int -> int -> int * int **)

  let rec pos_div_eucl a b =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = add (mul ((fun p->2*p) 1) r) 1 in
      if ltb r' b then ((mul ((fun p->2*p) 1) q), r') else ((add (mul ((fun p->2*p) 1) q) 1), (sub r' b)))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = mul ((fun p->2*p) 1) r in
      if ltb r' b then ((mul ((fun p->2*p) 1) q), r') else ((add (mul ((fun p->2*p) 1) q) 1), (sub r' b)))
      (fun _ -> if leb ((fun p->2*p) 1) b then (0, 1) else (1, 0))
      a

  (** val div_eucl : int -> int -> int * int **)

  let div_eucl a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (0, 0))
      (fun a' ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> (0, 0))
        (fun _ -> pos_div_eucl a' b)
        (fun b' ->
        let (q, r) = pos_div_eucl a' b' in
        ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
           (fun _ -> ((opp q), 0))
           (fun _ -> ((opp (add q 1)), (add b r)))
           (fun _ -> ((opp (add q 1)), (add b r)))
           r))
        b)
      (fun a' ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> (0, 0))
        (fun _ ->
        let (q, r) = pos_div_eucl a' b in
        ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
           (fun _ -> ((opp q), 0))
           (fun _ -> ((opp (add q 1)), (sub b r)))
           (fun _ -> ((opp (add q 1)), (sub b r)))
           r))
        (fun b' -> let (q, r) = pos_div_eucl a' b' in (q, (opp r)))
        b)
      a

  (** val div : int -> int -> int **)

  let div a b =
    let (q, _) = div_eucl a b in q

  (** val modulo : int -> int -> int **)

  let modulo a b =
    let (_, r) = div_eucl a b in r

  (** val quotrem : int -> int -> int * int **)

  let quotrem a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (0, 0))
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> (0, a))
        (fun b0 -> let (q, r) = Coq_N.pos_div_eucl a0 b0 in ((of_N q), (of_N r)))
        (fun b0 -> let (q, r) = Coq_N.pos_div_eucl a0 b0 in ((opp (of_N q)), (of_N r)))
        b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> (0, a))
        (fun b0 -> let (q, r) = Coq_N.pos_div_eucl a0 b0 in ((opp (of_N q)), (opp (of_N r))))
        (fun b0 -> let (q, r) = Coq_N.pos_div_eucl a0 b0 in ((of_N q), (opp (of_N r))))
        b)
      a

  (** val quot : int -> int -> int **)

  let quot a b =
    fst (quotrem a b)

  (** val rem : int -> int -> int **)

  let rem a b =
    snd (quotrem a b)

  (** val div2 : int -> int **)

  let div2 z =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> (Coq_Pos.div2 p))
        (fun _ -> (Coq_Pos.div2 p))
        (fun _ -> 0)
        p)
      (fun p -> (~-) (Coq_Pos.div2_up p))
      z

  (** val shiftl : int -> int -> int **)

  let shiftl a n =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> a)
      (fun p -> Coq_Pos.iter (mul ((fun p->2*p) 1)) a p)
      (fun p -> Coq_Pos.iter div2 a p)
      n

  (** val shiftr : int -> int -> int **)

  let shiftr a n =
    shiftl a (opp n)

  (** val coq_lor : int -> int -> int **)

  let coq_lor a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> a)
        (fun b0 -> (Coq_Pos.coq_lor a0 b0))
        (fun b0 -> (~-) (Coq_N.succ_pos (Coq_N.ldiff (Coq_Pos.pred_N b0) a0)))
        b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> a)
        (fun b0 -> (~-) (Coq_N.succ_pos (Coq_N.ldiff (Coq_Pos.pred_N a0) b0)))
        (fun b0 -> (~-) (Coq_N.succ_pos (Coq_N.coq_land (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))
        b)
      a

  (** val coq_land : int -> int -> int **)

  let coq_land a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> 0)
        (fun b0 -> of_N (Coq_Pos.coq_land a0 b0))
        (fun b0 -> of_N (Coq_N.ldiff a0 (Coq_Pos.pred_N b0)))
        b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> 0)
        (fun b0 -> of_N (Coq_N.ldiff b0 (Coq_Pos.pred_N a0)))
        (fun b0 -> (~-) (Coq_N.succ_pos (Coq_N.coq_lor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))
        b)
      a

  (** val ldiff : int -> int -> int **)

  let ldiff a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> a)
        (fun b0 -> of_N (Coq_Pos.ldiff a0 b0))
        (fun b0 -> of_N (Coq_N.coq_land a0 (Coq_Pos.pred_N b0)))
        b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> a)
        (fun b0 -> (~-) (Coq_N.succ_pos (Coq_N.coq_lor (Coq_Pos.pred_N a0) b0)))
        (fun b0 -> of_N (Coq_N.ldiff (Coq_Pos.pred_N b0) (Coq_Pos.pred_N a0)))
        b)
      a

  (** val coq_lxor : int -> int -> int **)

  let coq_lxor a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> a)
        (fun b0 -> of_N (Coq_Pos.coq_lxor a0 b0))
        (fun b0 -> (~-) (Coq_N.succ_pos (Coq_N.coq_lxor a0 (Coq_Pos.pred_N b0))))
        b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> a)
        (fun b0 -> (~-) (Coq_N.succ_pos (Coq_N.coq_lxor (Coq_Pos.pred_N a0) b0)))
        (fun b0 -> of_N (Coq_N.coq_lxor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0)))
        b)
      a

  (** val b2z : bool -> int **)

  let b2z = function
  | true -> 1
  | false -> 0

  (** val lnot : int -> int **)

  let lnot a =
    pred (opp a)
 end

(** val z_lt_dec : int -> int -> bool **)

let z_lt_dec x y =
  match Coq_Z.compare x y with
  | Lt -> true
  | _ -> false

(** val to_N : byte -> int **)

let to_N = function
| X00 -> 0
| X01 -> 1
| X02 -> ((fun p->2*p) 1)
| X03 -> ((fun p->1+2*p) 1)
| X04 -> ((fun p->2*p) ((fun p->2*p) 1))
| X05 -> ((fun p->1+2*p) ((fun p->2*p) 1))
| X06 -> ((fun p->2*p) ((fun p->1+2*p) 1))
| X07 -> ((fun p->1+2*p) ((fun p->1+2*p) 1))
| X08 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))
| X09 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))
| X0a -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))
| X0b -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))
| X0c -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))
| X0d -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))
| X0e -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))
| X0f -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))
| X10 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
| X11 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
| X12 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1))))
| X13 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1))))
| X14 -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))
| X15 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))
| X16 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))
| X17 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))
| X18 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))
| X19 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))
| X1a -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))
| X1b -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))
| X1c -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))
| X1d -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))
| X1e -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))
| X1f -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))
| X20 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))
| X21 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))
| X22 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))
| X23 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))
| X24 -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))))
| X25 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))))
| X26 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))))
| X27 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))))
| X28 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))
| X29 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))
| X2a -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))
| X2b -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))
| X2c -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))
| X2d -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))
| X2e -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))
| X2f -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))
| X30 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))
| X31 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))
| X32 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))
| X33 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))
| X34 -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))
| X35 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))
| X36 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))
| X37 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))
| X38 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))
| X39 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))
| X3a -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))
| X3b -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))
| X3c -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))
| X3d -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))
| X3e -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))
| X3f -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))
| X40 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))
| X41 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))
| X42 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))
| X43 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))
| X44 -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))
| X45 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))
| X46 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))
| X47 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))
| X48 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1))))))
| X49 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1))))))
| X4a -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1))))))
| X4b -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1))))))
| X4c -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1))))))
| X4d -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1))))))
| X4e -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1))))))
| X4f -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1))))))
| X50 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))))
| X51 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))))
| X52 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))))
| X53 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))))
| X54 -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))))
| X55 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))))
| X56 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))))
| X57 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))))
| X58 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))))
| X59 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))))
| X5a -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))))
| X5b -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))))
| X5c -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))))
| X5d -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))))
| X5e -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))))
| X5f -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))))
| X60 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))))
| X61 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))))
| X62 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))))
| X63 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))))
| X64 -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))))
| X65 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))))
| X66 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))))
| X67 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))))
| X68 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))))
| X69 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))))
| X6a -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))))
| X6b -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))))
| X6c -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))))
| X6d -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))))
| X6e -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))))
| X6f -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))))
| X70 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))))
| X71 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))))
| X72 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))))
| X73 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))))
| X74 -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))))
| X75 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))))
| X76 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))))
| X77 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))))
| X78 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))))
| X79 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))))
| X7a -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))))
| X7b -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))))
| X7c -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))))
| X7d -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))))
| X7e -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))))
| X7f -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))))
| X80 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| X81 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| X82 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| X83 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| X84 -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| X85 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| X86 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| X87 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| X88 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| X89 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| X8a -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| X8b -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| X8c -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| X8d -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| X8e -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| X8f -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| X90 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| X91 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| X92 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| X93 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| X94 -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| X95 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| X96 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| X97 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| X98 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| X99 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| X9a -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| X9b -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| X9c -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| X9d -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| X9e -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| X9f -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))
| Xa0 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xa1 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xa2 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xa3 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xa4 -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xa5 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xa6 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xa7 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xa8 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xa9 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xaa -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xab -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xac -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xad -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xae -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xaf -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xb0 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xb1 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xb2 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xb3 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xb4 -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xb5 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xb6 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xb7 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xb8 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xb9 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xba -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xbb -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xbc -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xbd -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xbe -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xbf -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))))
| Xc0 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xc1 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xc2 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xc3 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xc4 -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xc5 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xc6 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xc7 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xc8 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xc9 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xca -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xcb -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xcc -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xcd -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xce -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xcf -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xd0 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xd1 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xd2 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xd3 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xd4 -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xd5 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xd6 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xd7 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xd8 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xd9 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xda -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xdb -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xdc -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xdd -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xde -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xdf -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))))
| Xe0 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
| Xe1 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
| Xe2 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
| Xe3 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
| Xe4 -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
| Xe5 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
| Xe6 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
| Xe7 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
| Xe8 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
| Xe9 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
| Xea -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
| Xeb -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
| Xec -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
| Xed -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
| Xee -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
| Xef -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
| Xf0 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
| Xf1 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
| Xf2 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
| Xf3 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
| Xf4 -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
| Xf5 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
| Xf6 -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
| Xf7 -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
| Xf8 -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
| Xf9 -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
| Xfa -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
| Xfb -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
| Xfc -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
| Xfd -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
| Xfe -> ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
| Xff -> ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

(** val eqb0 : ascii -> ascii -> bool **)

let eqb0 a b =
  let Ascii (a0, a1, a2, a3, a4, a5, a6, a7) = a in
  let Ascii (b0, b1, b2, b3, b4, b5, b6, b7) = b in
  if if if if if if if eqb a0 b0 then eqb a1 b1 else false then eqb a2 b2 else false then eqb a3 b3 else false then eqb a4 b4 else false
        then eqb a5 b5
        else false
     then eqb a6 b6
     else false
  then eqb a7 b7
  else false

(** val n_of_digits : bool list -> int **)

let rec n_of_digits = function
| [] -> 0
| b :: l' -> Coq_N.add (if b then 1 else 0) (Coq_N.mul ((fun p->2*p) 1) (n_of_digits l'))

(** val n_of_ascii : ascii -> int **)

let n_of_ascii = function
| Ascii (a0, a1, a2, a3, a4, a5, a6, a7) -> n_of_digits (a0 :: (a1 :: (a2 :: (a3 :: (a4 :: (a5 :: (a6 :: (a7 :: []))))))))

type string =
| EmptyString
| String of ascii * string

module Coq_map =
 struct
  type ('key, 'value) map = { get : (__ -> 'key -> 'value option); empty : __; put : (__ -> 'key -> 'value -> __);
                              remove : (__ -> 'key -> __); fold : (__ -> (__ -> 'key -> 'value -> __) -> __ -> __ -> __) }
 end

module Coq_word =
 struct
  type word = { unsigned : (__ -> int); signed : (__ -> int); of_Z : (int -> __); add : (__ -> __ -> __); sub : (__ -> __ -> __);
                opp : (__ -> __); coq_or : (__ -> __ -> __); coq_and : (__ -> __ -> __); xor : (__ -> __ -> __); not : (__ -> __);
                ndn : (__ -> __ -> __); mul : (__ -> __ -> __); mulhss : (__ -> __ -> __); mulhsu : (__ -> __ -> __);
                mulhuu : (__ -> __ -> __); divu : (__ -> __ -> __); divs : (__ -> __ -> __); modu : (__ -> __ -> __);
                mods : (__ -> __ -> __); slu : (__ -> __ -> __); sru : (__ -> __ -> __); srs : (__ -> __ -> __); eqb : (__ -> __ -> bool);
                ltu : (__ -> __ -> bool); lts : (__ -> __ -> bool); sextend : (int -> __ -> __) }

  type rep = __

  (** val unsigned : int -> word -> rep -> int **)

  let unsigned _ word2 =
    word2.unsigned

  (** val of_Z : int -> word -> int -> rep **)

  let of_Z _ word2 =
    word2.of_Z

  (** val add : int -> word -> rep -> rep -> rep **)

  let add _ word2 =
    word2.add

  (** val sub : int -> word -> rep -> rep -> rep **)

  let sub _ word2 =
    word2.sub

  (** val coq_or : int -> word -> rep -> rep -> rep **)

  let coq_or _ word2 =
    word2.coq_or

  (** val coq_and : int -> word -> rep -> rep -> rep **)

  let coq_and _ word2 =
    word2.coq_and

  (** val xor : int -> word -> rep -> rep -> rep **)

  let xor _ word2 =
    word2.xor

  (** val mul : int -> word -> rep -> rep -> rep **)

  let mul _ word2 =
    word2.mul

  (** val mulhuu : int -> word -> rep -> rep -> rep **)

  let mulhuu _ word2 =
    word2.mulhuu

  (** val divu : int -> word -> rep -> rep -> rep **)

  let divu _ word2 =
    word2.divu

  (** val modu : int -> word -> rep -> rep -> rep **)

  let modu _ word2 =
    word2.modu

  (** val slu : int -> word -> rep -> rep -> rep **)

  let slu _ word2 =
    word2.slu

  (** val sru : int -> word -> rep -> rep -> rep **)

  let sru _ word2 =
    word2.sru

  (** val srs : int -> word -> rep -> rep -> rep **)

  let srs _ word2 =
    word2.srs

  (** val eqb : int -> word -> rep -> rep -> bool **)

  let eqb _ word2 =
    word2.eqb

  (** val ltu : int -> word -> rep -> rep -> bool **)

  let ltu _ word2 =
    word2.ltu

  (** val lts : int -> word -> rep -> rep -> bool **)

  let lts _ word2 =
    word2.lts
 end

module Coq_byte =
 struct
  (** val unsigned : byte -> int **)

  let unsigned b =
    Coq_Z.of_N (to_N b)
 end

module Coq_bopname =
 struct
  type bopname =
  | Coq_add
  | Coq_sub
  | Coq_mul
  | Coq_mulhuu
  | Coq_divu
  | Coq_remu
  | Coq_and
  | Coq_or
  | Coq_xor
  | Coq_sru
  | Coq_slu
  | Coq_srs
  | Coq_lts
  | Coq_ltu
  | Coq_eq
 end

module Coq_access_size =
 struct
  type access_size =
  | Coq_one
  | Coq_two
  | Coq_four
  | Coq_word
 end

module Coq_expr =
 struct
  type expr =
  | Coq_literal of int
  | Coq_var of string
  | Coq_load of Coq_access_size.access_size * expr
  | Coq_op of Coq_bopname.bopname * expr * expr
 end

module Coq_cmd =
 struct
  type cmd =
  | Coq_skip
  | Coq_set of string * Coq_expr.expr
  | Coq_unset of string
  | Coq_store of Coq_access_size.access_size * Coq_expr.expr * Coq_expr.expr
  | Coq_stackalloc of string * int * cmd
  | Coq_cond of Coq_expr.expr * cmd * cmd
  | Coq_seq of cmd * cmd
  | Coq_while of Coq_expr.expr * cmd
  | Coq_call of string list * string * Coq_expr.expr list
  | Coq_interact of string list * string * Coq_expr.expr list
 end

(** val bytes_per_word : int -> int **)

let bytes_per_word width0 =
  Coq_Z.div (Coq_Z.add width0 ((fun p->1+2*p) ((fun p->1+2*p) 1))) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))

(** val bytes_per : int -> Coq_access_size.access_size -> nat **)

let bytes_per width0 = function
| Coq_access_size.Coq_one -> S O
| Coq_access_size.Coq_two -> S (S O)
| Coq_access_size.Coq_four -> S (S (S (S O)))
| Coq_access_size.Coq_word -> Z.to_nat (bytes_per_word width0)

type parameters = { width : int; word0 : Coq_word.word; mem : (Coq_word.rep, byte) Coq_map.map;
                    locals : (string, Coq_word.rep) Coq_map.map; env : (string, (string list * string list) * Coq_cmd.cmd) Coq_map.map }

module Coq_parameters =
 struct
  type parameters = __ -> __ -> bool
    (* singleton inductive, whose constructor was Build_parameters *)

  type key = __

  type value = __

  (** val ltb : parameters -> key -> key -> bool **)

  let ltb parameters1 =
    parameters1
 end

(** val eqb1 : Coq_parameters.parameters -> Coq_parameters.key -> Coq_parameters.key -> bool **)

let eqb1 p k1 k2 =
  (&&) (negb (Coq_parameters.ltb p k1 k2)) (negb (Coq_parameters.ltb p k2 k1))

(** val put0 :
    Coq_parameters.parameters -> (Coq_parameters.key * Coq_parameters.value) list -> Coq_parameters.key -> Coq_parameters.value ->
    (Coq_parameters.key * Coq_parameters.value) list **)

let rec put0 p m k v =
  match m with
  | [] -> (k, v) :: []
  | y :: m' ->
    let (k', v') = y in
    if Coq_parameters.ltb p k k' then (k, v) :: m else if Coq_parameters.ltb p k' k then (k', v') :: (put0 p m' k v) else (k, v) :: m'

(** val remove0 :
    Coq_parameters.parameters -> (Coq_parameters.key * Coq_parameters.value) list -> Coq_parameters.key ->
    (Coq_parameters.key * Coq_parameters.value) list **)

let rec remove0 p m k =
  match m with
  | [] -> []
  | y :: m' ->
    let (k', v') = y in if Coq_parameters.ltb p k k' then m else if Coq_parameters.ltb p k' k then (k', v') :: (remove0 p m' k) else m'

type rep0 = (Coq_parameters.key * Coq_parameters.value) list
  (* singleton inductive, whose constructor was Build_rep *)

(** val value0 : Coq_parameters.parameters -> rep0 -> (Coq_parameters.key * Coq_parameters.value) list **)

let value0 _ r =
  r

(** val lookup :
    Coq_parameters.parameters -> (Coq_parameters.key * Coq_parameters.value) list -> Coq_parameters.key -> Coq_parameters.value option **)

let lookup p l k =
  match find (fun p0 -> eqb1 p k (fst p0)) l with
  | Some p0 -> let (_, v) = p0 in Some v
  | None -> None

(** val map0 : Coq_parameters.parameters -> (Coq_parameters.key, Coq_parameters.value) Coq_map.map **)

let map0 p =
  let wrapped_put = fun m k v -> put0 p (value0 p m) k v in
  let wrapped_remove = fun m k -> remove0 p (value0 p m) k in
  { Coq_map.get = (fun m k -> lookup p (value0 p (Obj.magic m)) k); Coq_map.empty = (Obj.magic []); Coq_map.put = (Obj.magic wrapped_put);
  Coq_map.remove = (Obj.magic wrapped_remove); Coq_map.fold = (fun _ f r0 m ->
  fold_right (fun pat r -> let (k, v) = pat in f r k v) r0 (value0 p (Obj.magic m))) }

module Ascii =
 struct
  (** val ltb : ascii -> ascii -> bool **)

  let ltb c d =
    N.ltb (n_of_ascii c) (n_of_ascii d)
 end

(** val ltb0 : string -> string -> bool **)

let rec ltb0 a b =
  match a with
  | EmptyString -> (match b with
                    | EmptyString -> false
                    | String (_, _) -> true)
  | String (x, a') -> (match b with
                       | EmptyString -> false
                       | String (y, b') -> if eqb0 x y then ltb0 a' b' else Ascii.ltb x y)

(** val build_parameters : Coq_parameters.parameters **)

let build_parameters =
  Obj.magic ltb0

(** val map1 : (Coq_parameters.key, Coq_parameters.value) Coq_map.map **)

let map1 =
  map0 build_parameters

(** val nlet : string list -> 'a1 -> ('a1 -> 'a2) -> 'a2 **)

let nlet _ a0 body =
  body a0

module ExprReflection =
 struct
  type 't expr_reifier = { er_T2w : ('t -> Coq_word.rep); er_default : 't; er_opfun : (__ -> 't -> 't -> 't);
                           er_opname : (__ -> Coq_bopname.bopname) }

  type 't er_op = __

  (** val er_opname : parameters -> 'a1 expr_reifier -> 'a1 er_op -> Coq_bopname.bopname **)

  let er_opname _ expr_reifier0 =
    expr_reifier0.er_opname

  type 't coq_AST =
  | ELit of int * 't * __ option
  | EVar of string
  | EOp of 't er_op * 't coq_AST * 't coq_AST

  (** val compile : parameters -> 'a1 expr_reifier -> 'a1 coq_AST -> Coq_expr.expr **)

  let rec compile semantics0 er = function
  | ELit (z, _, _) -> Coq_expr.Coq_literal z
  | EVar nm -> Coq_expr.Coq_var nm
  | EOp (op, l, r) -> Coq_expr.Coq_op ((er.er_opname op), (compile semantics0 er l), (compile semantics0 er r))

  (** val expr_word_reifier : parameters -> Coq_word.rep expr_reifier **)

  let expr_word_reifier semantics0 =
    { er_T2w = (fun w -> w); er_default = (semantics0.word0.Coq_word.of_Z 0); er_opfun = (fun op ->
      match Obj.magic op with
      | Coq_bopname.Coq_add -> semantics0.word0.Coq_word.add
      | Coq_bopname.Coq_sub -> semantics0.word0.Coq_word.sub
      | Coq_bopname.Coq_mul -> semantics0.word0.Coq_word.mul
      | Coq_bopname.Coq_mulhuu -> semantics0.word0.Coq_word.mulhuu
      | Coq_bopname.Coq_divu -> semantics0.word0.Coq_word.divu
      | Coq_bopname.Coq_remu -> semantics0.word0.Coq_word.modu
      | Coq_bopname.Coq_and -> semantics0.word0.Coq_word.coq_and
      | Coq_bopname.Coq_or -> semantics0.word0.Coq_word.coq_or
      | Coq_bopname.Coq_xor -> semantics0.word0.Coq_word.xor
      | Coq_bopname.Coq_sru -> semantics0.word0.Coq_word.sru
      | Coq_bopname.Coq_slu -> semantics0.word0.Coq_word.slu
      | Coq_bopname.Coq_srs -> semantics0.word0.Coq_word.srs
      | Coq_bopname.Coq_lts -> (fun x y -> semantics0.word0.Coq_word.of_Z (Coq_Z.b2z (semantics0.word0.Coq_word.lts x y)))
      | Coq_bopname.Coq_ltu -> (fun x y -> semantics0.word0.Coq_word.of_Z (Coq_Z.b2z (semantics0.word0.Coq_word.ltu x y)))
      | Coq_bopname.Coq_eq -> (fun x y -> semantics0.word0.Coq_word.of_Z (Coq_Z.b2z (semantics0.word0.Coq_word.eqb x y)))); er_opname =
      (fun op -> Obj.magic op) }
 end

(** val is_skip : Coq_cmd.cmd -> bool **)

let is_skip = function
| Coq_cmd.Coq_skip -> true
| _ -> false

(** val noskips : Coq_cmd.cmd -> Coq_cmd.cmd **)

let rec noskips c = match c with
| Coq_cmd.Coq_stackalloc (lhs, nbytes, body) -> Coq_cmd.Coq_stackalloc (lhs, nbytes, (noskips body))
| Coq_cmd.Coq_cond (condition, nonzero_branch, zero_branch) ->
  Coq_cmd.Coq_cond (condition, (noskips nonzero_branch), (noskips zero_branch))
| Coq_cmd.Coq_seq (s1, s2) ->
  let s3 = noskips s1 in let s4 = noskips s2 in if is_skip s3 then s4 else if is_skip s4 then s3 else Coq_cmd.Coq_seq (s3, s4)
| Coq_cmd.Coq_while (test, body) -> Coq_cmd.Coq_while (test, (noskips body))
| _ -> c

type 't hasDefault = 't

(** val default : 'a1 hasDefault -> 'a1 **)

let default hasDefault0 =
  hasDefault0

(** val hasDefault_byte : byte hasDefault **)

let hasDefault_byte =
  X00

type ('t1, 't2) convertible = 't1 -> 't2

(** val cast : ('a1, 'a2) convertible -> 'a1 -> 'a2 **)

let cast convertible0 =
  convertible0

module ListArray =
 struct
  type 'v t = 'v list

  (** val get : 'a2 hasDefault -> ('a1, nat) convertible -> 'a2 t -> 'a1 -> 'a2 **)

  let get hD conv a k =
    nth (cast conv k) a (default hD)
 end

(** val offset : Coq_expr.expr -> Coq_expr.expr -> Coq_expr.expr -> Coq_expr.expr **)

let offset base idx width0 =
  Coq_expr.Coq_op (Coq_bopname.Coq_add, base, (Coq_expr.Coq_op (Coq_bopname.Coq_mul, width0, idx)))

(** val convertible_word_nat : parameters -> (Coq_word.rep, nat) convertible **)

let convertible_word_nat s w =
  Coq_Z.to_nat (s.word0.Coq_word.unsigned w)

(** val sortedList_parameters : int -> Coq_word.word -> Coq_parameters.parameters **)

let sortedList_parameters _ word2 =
  word2.Coq_word.ltu

(** val map2 : int -> Coq_word.word -> (Coq_word.rep, 'a1) Coq_map.map **)

let map2 width0 word2 =
  Obj.magic map0 (sortedList_parameters width0 word2)

type rep1 = int
  (* singleton inductive, whose constructor was mk *)

(** val unsigned0 : int -> rep1 -> int **)

let unsigned0 _ r =
  r

(** val wrap : int -> int -> rep1 **)

let wrap width0 z =
  Coq_Z.modulo z (Coq_Z.pow ((fun p->2*p) 1) width0)

(** val signed0 : int -> rep1 -> int **)

let signed0 width0 =
  let wrap_value = fun z -> Coq_Z.modulo z (Coq_Z.pow ((fun p->2*p) 1) width0) in
  let swrap_value = fun z ->
    Coq_Z.sub (wrap_value (Coq_Z.add z (Coq_Z.pow ((fun p->2*p) 1) (Coq_Z.sub width0 1))))
      (Coq_Z.pow ((fun p->2*p) 1) (Coq_Z.sub width0 1))
  in
  (fun w -> swrap_value (unsigned0 width0 w))

(** val word1 : int -> Coq_word.word **)

let word1 width0 =
  { Coq_word.unsigned = (Obj.magic unsigned0 width0); Coq_word.signed = (Obj.magic signed0 width0); Coq_word.of_Z =
    (Obj.magic wrap width0); Coq_word.add = (fun x y ->
    Obj.magic wrap width0 (Coq_Z.add (unsigned0 width0 (Obj.magic x)) (unsigned0 width0 (Obj.magic y)))); Coq_word.sub = (fun x y ->
    Obj.magic wrap width0 (Coq_Z.sub (unsigned0 width0 (Obj.magic x)) (unsigned0 width0 (Obj.magic y)))); Coq_word.opp = (fun x ->
    Obj.magic wrap width0 (Coq_Z.opp (unsigned0 width0 (Obj.magic x)))); Coq_word.coq_or = (fun x y ->
    Obj.magic wrap width0 (Coq_Z.coq_lor (unsigned0 width0 (Obj.magic x)) (unsigned0 width0 (Obj.magic y)))); Coq_word.coq_and =
    (fun x y -> Obj.magic wrap width0 (Coq_Z.coq_land (unsigned0 width0 (Obj.magic x)) (unsigned0 width0 (Obj.magic y)))); Coq_word.xor =
    (fun x y -> Obj.magic wrap width0 (Coq_Z.coq_lxor (unsigned0 width0 (Obj.magic x)) (unsigned0 width0 (Obj.magic y)))); Coq_word.not =
    (fun x -> Obj.magic wrap width0 (Coq_Z.lnot (unsigned0 width0 (Obj.magic x)))); Coq_word.ndn = (fun x y ->
    Obj.magic wrap width0 (Coq_Z.ldiff (unsigned0 width0 (Obj.magic x)) (unsigned0 width0 (Obj.magic y)))); Coq_word.mul = (fun x y ->
    Obj.magic wrap width0 (Coq_Z.mul (unsigned0 width0 (Obj.magic x)) (unsigned0 width0 (Obj.magic y)))); Coq_word.mulhss = (fun x y ->
    Obj.magic wrap width0
      (Coq_Z.div (Coq_Z.mul (signed0 width0 (Obj.magic x)) (signed0 width0 (Obj.magic y))) (Coq_Z.pow ((fun p->2*p) 1) width0)));
    Coq_word.mulhsu = (fun x y ->
    Obj.magic wrap width0
      (Coq_Z.div (Coq_Z.mul (signed0 width0 (Obj.magic x)) (unsigned0 width0 (Obj.magic y))) (Coq_Z.pow ((fun p->2*p) 1) width0)));
    Coq_word.mulhuu = (fun x y ->
    Obj.magic wrap width0
      (Coq_Z.div (Coq_Z.mul (unsigned0 width0 (Obj.magic x)) (unsigned0 width0 (Obj.magic y))) (Coq_Z.pow ((fun p->2*p) 1) width0)));
    Coq_word.divu = (fun x y -> Obj.magic wrap width0 (Coq_Z.div (unsigned0 width0 (Obj.magic x)) (unsigned0 width0 (Obj.magic y))));
    Coq_word.divs = (fun x y -> Obj.magic wrap width0 (Coq_Z.quot (signed0 width0 (Obj.magic x)) (signed0 width0 (Obj.magic y))));
    Coq_word.modu = (fun x y -> Obj.magic wrap width0 (Coq_Z.modulo (unsigned0 width0 (Obj.magic x)) (unsigned0 width0 (Obj.magic y))));
    Coq_word.mods = (fun x y -> Obj.magic wrap width0 (Coq_Z.rem (signed0 width0 (Obj.magic x)) (signed0 width0 (Obj.magic y))));
    Coq_word.slu = (fun x y -> Obj.magic wrap width0 (Coq_Z.shiftl (unsigned0 width0 (Obj.magic x)) (unsigned0 width0 (Obj.magic y))));
    Coq_word.sru = (fun x y -> Obj.magic wrap width0 (Coq_Z.shiftr (unsigned0 width0 (Obj.magic x)) (unsigned0 width0 (Obj.magic y))));
    Coq_word.srs = (fun x y -> Obj.magic wrap width0 (Coq_Z.shiftr (signed0 width0 (Obj.magic x)) (unsigned0 width0 (Obj.magic y))));
    Coq_word.eqb = (fun x y -> Coq_Z.eqb (unsigned0 width0 (Obj.magic x)) (unsigned0 width0 (Obj.magic y))); Coq_word.ltu = (fun x y ->
    Coq_Z.ltb (unsigned0 width0 (Obj.magic x)) (unsigned0 width0 (Obj.magic y))); Coq_word.lts = (fun x y ->
    Coq_Z.ltb (signed0 width0 (Obj.magic x)) (signed0 width0 (Obj.magic y))); Coq_word.sextend = (fun oldwidth z ->
    Obj.magic wrap width0
      (Coq_Z.sub
        (Coq_Z.modulo (Coq_Z.add (unsigned0 width0 (Obj.magic z)) (Coq_Z.pow ((fun p->2*p) 1) (Coq_Z.sub oldwidth 1)))
          (Coq_Z.pow ((fun p->2*p) 1) oldwidth)) (Coq_Z.pow ((fun p->2*p) 1) (Coq_Z.sub oldwidth 1)))) }

module ExitToken =
 struct
  type t = bool

  (** val coq_new : bool -> t **)

  let coq_new b =
    b

  (** val get : t -> bool **)

  let get tok =
    tok
 end

(** val ranged_for' : int -> int -> int -> (ExitToken.t -> int -> 'a1 -> __ -> ExitToken.t * 'a1) -> 'a1 -> int -> 'a1 **)

let rec ranged_for' from to0 step body x x0 =
  if z_lt_dec x0 to0
  then let (tok, a1) = body (ExitToken.coq_new false) x0 x __ in
       if ExitToken.get tok then a1 else ranged_for' from to0 step body a1 (Coq_Z.add x0 (Coq_Z.max 1 step))
  else x

(** val ranged_for : int -> int -> int -> (ExitToken.t -> int -> 'a1 -> __ -> ExitToken.t * 'a1) -> 'a1 -> 'a1 **)

let ranged_for from to0 step body a0 =
  ranged_for' from to0 step body a0 from

(** val ranged_for_w :
    parameters -> Coq_word.rep -> Coq_word.rep -> Coq_word.rep -> (Coq_word.rep -> int) -> (ExitToken.t -> Coq_word.rep -> 'a1 -> __ ->
    ExitToken.t * 'a1) -> 'a1 -> 'a1 **)

let ranged_for_w semantics0 from to0 step to_Z body a0 =
  ranged_for (to_Z from) (to_Z to0) (to_Z step) (fun tok idx acc _ -> body tok (semantics0.word0.Coq_word.of_Z idx) acc __) a0

(** val ranged_for_u :
    parameters -> Coq_word.rep -> Coq_word.rep -> Coq_word.rep -> (ExitToken.t -> Coq_word.rep -> 'a1 -> __ -> ExitToken.t * 'a1) -> 'a1
    -> 'a1 **)

let ranged_for_u semantics0 from to0 step =
  ranged_for_w semantics0 from to0 step semantics0.word0.Coq_word.unsigned

(** val parameters0 : parameters **)

let parameters0 =
  let word2 = word1 ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))) in
  { width = ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))); word0 = word2; mem =
  (map2 ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))) word2); locals = (Obj.magic map1); env =
  (Obj.magic map1) }

module type FNV1A_params =
 sig
  val semantics : parameters

  val prime : Coq_word.rep

  val offset : Coq_word.rep
 end

module FNV1A =
 functor (P:FNV1A_params) ->
 struct
  (** val update : Coq_word.rep -> Coq_word.rep -> Coq_word.rep **)

  let update hash data =
    nlet ((String ((Ascii (false, false, false, false, true, true, true, false)), EmptyString)) :: []) P.prime (fun p ->
      nlet ((String ((Ascii (false, false, false, true, false, true, true, false)), (String ((Ascii (true, false, false, false, false,
        true, true, false)), (String ((Ascii (true, true, false, false, true, true, true, false)), (String ((Ascii (false, false, false,
        true, false, true, true, false)), EmptyString)))))))) :: []) (P.semantics.word0.Coq_word.xor hash data) (fun hash0 ->
        nlet ((String ((Ascii (false, false, false, true, false, true, true, false)), (String ((Ascii (true, false, false, false, false,
          true, true, false)), (String ((Ascii (true, true, false, false, true, true, true, false)), (String ((Ascii (false, false, false,
          true, false, true, true, false)), EmptyString)))))))) :: []) (P.semantics.word0.Coq_word.mul hash0 p) (fun hash1 -> hash1)))

  (** val update_body : Coq_cmd.cmd **)

  let update_body =
    noskips (Coq_cmd.Coq_seq ((Coq_cmd.Coq_set ((String ((Ascii (false, false, false, false, true, true, true, false)), EmptyString)),
      (Coq_expr.Coq_literal (P.semantics.word0.Coq_word.unsigned P.prime)))), (Coq_cmd.Coq_seq ((Coq_cmd.Coq_set ((String ((Ascii (false,
      false, false, true, false, true, true, false)), (String ((Ascii (true, false, false, false, false, true, true, false)), (String
      ((Ascii (true, true, false, false, true, true, true, false)), (String ((Ascii (false, false, false, true, false, true, true,
      false)), EmptyString)))))))),
      (ExprReflection.compile P.semantics (ExprReflection.expr_word_reifier P.semantics) (ExprReflection.EOp
        ((Obj.magic Coq_bopname.Coq_xor), (ExprReflection.EVar (String ((Ascii (false, false, false, true, false, true, true, false)),
        (String ((Ascii (true, false, false, false, false, true, true, false)), (String ((Ascii (true, true, false, false, true, true,
        true, false)), (String ((Ascii (false, false, false, true, false, true, true, false)), EmptyString))))))))), (ExprReflection.EVar
        (String ((Ascii (false, false, true, false, false, true, true, false)), (String ((Ascii (true, false, false, false, false, true,
        true, false)), (String ((Ascii (false, false, true, false, true, true, true, false)), (String ((Ascii (true, false, false, false,
        false, true, true, false)), EmptyString)))))))))))))), (Coq_cmd.Coq_seq ((Coq_cmd.Coq_set ((String ((Ascii (false, false, false,
      true, false, true, true, false)), (String ((Ascii (true, false, false, false, false, true, true, false)), (String ((Ascii (true,
      true, false, false, true, true, true, false)), (String ((Ascii (false, false, false, true, false, true, true, false)),
      EmptyString)))))))),
      (ExprReflection.compile P.semantics (ExprReflection.expr_word_reifier P.semantics) (ExprReflection.EOp
        ((Obj.magic Coq_bopname.Coq_mul), (ExprReflection.EVar (String ((Ascii (false, false, false, true, false, true, true, false)),
        (String ((Ascii (true, false, false, false, false, true, true, false)), (String ((Ascii (true, true, false, false, true, true,
        true, false)), (String ((Ascii (false, false, false, true, false, true, true, false)), EmptyString))))))))), (ExprReflection.EVar
        (String ((Ascii (false, false, false, false, true, true, true, false)), EmptyString)))))))),
      (fold_right (fun v c -> Coq_cmd.Coq_seq ((Coq_cmd.Coq_unset v), c)) Coq_cmd.Coq_skip [])))))))

  (** val fnv1a : byte ListArray.t -> Coq_word.rep -> Coq_word.rep **)

  let fnv1a data len =
    nlet ((String ((Ascii (false, false, false, false, true, true, true, false)), EmptyString)) :: []) P.prime (fun p ->
      nlet ((String ((Ascii (false, false, false, true, false, true, true, false)), (String ((Ascii (true, false, false, false, false,
        true, true, false)), (String ((Ascii (true, true, false, false, true, true, true, false)), (String ((Ascii (false, false, false,
        true, false, true, true, false)), EmptyString)))))))) :: []) P.offset (fun hash ->
        nlet ((String ((Ascii (false, true, true, false, false, true, true, false)), (String ((Ascii (false, true, false, false, true,
          true, true, false)), (String ((Ascii (true, true, true, true, false, true, true, false)), (String ((Ascii (true, false, true,
          true, false, true, true, false)), EmptyString)))))))) :: []) (P.semantics.word0.Coq_word.of_Z 0) (fun from ->
          nlet ((String ((Ascii (true, true, false, false, true, true, true, false)), (String ((Ascii (false, false, true, false, true,
            true, true, false)), (String ((Ascii (true, false, true, false, false, true, true, false)), (String ((Ascii (false, false,
            false, false, true, true, true, false)), EmptyString)))))))) :: []) (P.semantics.word0.Coq_word.of_Z 1) (fun step ->
            nlet ((String ((Ascii (false, false, false, true, false, true, true, false)), (String ((Ascii (true, false, false, false,
              false, true, true, false)), (String ((Ascii (true, true, false, false, true, true, true, false)), (String ((Ascii (false,
              false, false, true, false, true, true, false)), EmptyString)))))))) :: [])
              (ranged_for_u P.semantics from len step (fun tok idx hash0 _ ->
                nlet ((String ((Ascii (false, true, false, false, false, true, true, false)), EmptyString)) :: [])
                  (ListArray.get hasDefault_byte (convertible_word_nat P.semantics) data idx) (fun b ->
                  nlet ((String ((Ascii (false, false, false, true, false, true, true, false)), (String ((Ascii (true, false, false,
                    false, false, true, true, false)), (String ((Ascii (true, true, false, false, true, true, true, false)), (String
                    ((Ascii (false, false, false, true, false, true, true, false)), EmptyString)))))))) :: [])
                    (P.semantics.word0.Coq_word.mul
                      (P.semantics.word0.Coq_word.xor hash0 (P.semantics.word0.Coq_word.of_Z (Coq_byte.unsigned b))) p) (fun hash1 ->
                    (tok, hash1)))) hash) (fun hash0 -> hash0)))))

  (** val fnv1a_body : Coq_cmd.cmd **)

  let fnv1a_body =
    noskips (Coq_cmd.Coq_seq ((Coq_cmd.Coq_set ((String ((Ascii (false, false, false, false, true, true, true, false)), EmptyString)),
      (Coq_expr.Coq_literal (P.semantics.word0.Coq_word.unsigned P.prime)))), (Coq_cmd.Coq_seq ((Coq_cmd.Coq_set ((String ((Ascii (false,
      false, false, true, false, true, true, false)), (String ((Ascii (true, false, false, false, false, true, true, false)), (String
      ((Ascii (true, true, false, false, true, true, true, false)), (String ((Ascii (false, false, false, true, false, true, true,
      false)), EmptyString)))))))), (Coq_expr.Coq_literal (P.semantics.word0.Coq_word.unsigned P.offset)))), (Coq_cmd.Coq_seq
      ((Coq_cmd.Coq_set ((String ((Ascii (false, true, true, false, false, true, true, false)), (String ((Ascii (false, true, false,
      false, true, true, true, false)), (String ((Ascii (true, true, true, true, false, true, true, false)), (String ((Ascii (true, false,
      true, true, false, true, true, false)), EmptyString)))))))),
      (ExprReflection.compile P.semantics (ExprReflection.expr_word_reifier P.semantics) (ExprReflection.ELit (0,
        (P.semantics.word0.Coq_word.of_Z 0), (Some __)))))), (Coq_cmd.Coq_seq ((Coq_cmd.Coq_set ((String ((Ascii (true, true, false,
      false, true, true, true, false)), (String ((Ascii (false, false, true, false, true, true, true, false)), (String ((Ascii (true,
      false, true, false, false, true, true, false)), (String ((Ascii (false, false, false, false, true, true, true, false)),
      EmptyString)))))))),
      (ExprReflection.compile P.semantics (ExprReflection.expr_word_reifier P.semantics) (ExprReflection.ELit (1,
        (P.semantics.word0.Coq_word.of_Z 1), (Some __)))))), (Coq_cmd.Coq_seq ((Coq_cmd.Coq_while ((Coq_expr.Coq_op (Coq_bopname.Coq_ltu,
      (Coq_expr.Coq_var (String ((Ascii (false, true, true, false, false, true, true, false)), (String ((Ascii (false, true, false, false,
      true, true, true, false)), (String ((Ascii (true, true, true, true, false, true, true, false)), (String ((Ascii (true, false, true,
      true, false, true, true, false)), EmptyString))))))))), (Coq_expr.Coq_var (String ((Ascii (false, false, true, true, false, true,
      true, false)), (String ((Ascii (true, false, true, false, false, true, true, false)), (String ((Ascii (false, true, true, true,
      false, true, true, false)), EmptyString))))))))), (Coq_cmd.Coq_seq ((Coq_cmd.Coq_seq ((Coq_cmd.Coq_set ((String ((Ascii (false,
      true, false, false, false, true, true, false)), EmptyString)), (Coq_expr.Coq_load (Coq_access_size.Coq_one,
      (offset (Coq_expr.Coq_var (String ((Ascii (false, false, true, false, false, true, true, false)), (String ((Ascii (true, false,
        false, false, false, true, true, false)), (String ((Ascii (false, false, true, false, true, true, true, false)), (String ((Ascii
        (true, false, false, false, false, true, true, false)), EmptyString))))))))) (Coq_expr.Coq_var (String ((Ascii (false, true, true,
        false, false, true, true, false)), (String ((Ascii (false, true, false, false, true, true, true, false)), (String ((Ascii (true,
        true, true, true, false, true, true, false)), (String ((Ascii (true, false, true, true, false, true, true, false)),
        EmptyString))))))))) (Coq_expr.Coq_literal (Coq_Z.of_nat (bytes_per P.semantics.width Coq_access_size.Coq_one)))))))),
      (Coq_cmd.Coq_seq ((Coq_cmd.Coq_set ((String ((Ascii (false, false, false, true, false, true, true, false)), (String ((Ascii (true,
      false, false, false, false, true, true, false)), (String ((Ascii (true, true, false, false, true, true, true, false)), (String
      ((Ascii (false, false, false, true, false, true, true, false)), EmptyString)))))))),
      (ExprReflection.compile P.semantics (ExprReflection.expr_word_reifier P.semantics) (ExprReflection.EOp
        ((Obj.magic Coq_bopname.Coq_mul), (ExprReflection.EOp ((Obj.magic Coq_bopname.Coq_xor), (ExprReflection.EVar (String ((Ascii
        (false, false, false, true, false, true, true, false)), (String ((Ascii (true, false, false, false, false, true, true, false)),
        (String ((Ascii (true, true, false, false, true, true, true, false)), (String ((Ascii (false, false, false, true, false, true,
        true, false)), EmptyString))))))))), (ExprReflection.EVar (String ((Ascii (false, true, false, false, false, true, true, false)),
        EmptyString))))), (ExprReflection.EVar (String ((Ascii (false, false, false, false, true, true, true, false)), EmptyString)))))))),
      (fold_right (fun v c -> Coq_cmd.Coq_seq ((Coq_cmd.Coq_unset v), c)) Coq_cmd.Coq_skip ((String ((Ascii (false, true, false, false,
        false, true, true, false)), EmptyString)) :: [])))))), (Coq_cmd.Coq_set ((String ((Ascii (false, true, true, false, false, true,
      true, false)), (String ((Ascii (false, true, false, false, true, true, true, false)), (String ((Ascii (true, true, true, true,
      false, true, true, false)), (String ((Ascii (true, false, true, true, false, true, true, false)), EmptyString)))))))),
      (Coq_expr.Coq_op (Coq_bopname.Coq_add, (Coq_expr.Coq_var (String ((Ascii (false, true, true, false, false, true, true, false)),
      (String ((Ascii (false, true, false, false, true, true, true, false)), (String ((Ascii (true, true, true, true, false, true, true,
      false)), (String ((Ascii (true, false, true, true, false, true, true, false)), EmptyString))))))))), (Coq_expr.Coq_literal
      1))))))))), (fold_right (fun v c -> Coq_cmd.Coq_seq ((Coq_cmd.Coq_unset v), c)) Coq_cmd.Coq_skip [])))))))))))
 end

module FNV1A32_params =
 struct
  (** val semantics : parameters **)

  let semantics =
    parameters0

  (** val prime : Coq_word.rep **)

  let prime =
    Obj.magic ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
      ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))))))))))))))))))))

  (** val offset : Coq_word.rep **)

  let offset =
    Obj.magic ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))))))))))))))))))))))))))
 end

module FNV1A32 = FNV1A(FNV1A32_params)

(** val fnv1a0 : byte ListArray.t -> int -> Coq_word.rep **)

let fnv1a0 data len =
  FNV1A32.fnv1a data (FNV1A32_params.semantics.word0.Coq_word.of_Z len)
