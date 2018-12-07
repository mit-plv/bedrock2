Require Import Coq.NArith.BinNatDef.
Require Import bedrock2.Syntax bedrock2.BasicC64Syntax bedrock2.Semantics.
Require bedrock2.String bedrock2.Map.SortedList bedrock2.Map.SortedListString.
Require Import coqutil.Word.Interface coqutil.Datatypes.HList coqutil.Datatypes.PrimitivePair.
Require coqutil.Word.Naive.
Import ZArith.
Definition word := Word.Naive.word 64 (proj2 (Zlt_is_lt_bool 0 64) eq_refl).
Definition byte := Word.Naive.word 8 (proj2 (Zlt_is_lt_bool 0 8) eq_refl).
Definition bytes_per sz := match sz with access_size.one => 1 | access_size.two => 2 | access_size.four => 4 | access_size.word => 8 end.
Fixpoint combine (n : nat) : forall (bs : tuple byte n), word :=
  match n with
  | O => fun _ => word.of_Z 0
  | S n => fun bs => word.or (word.of_Z (word.unsigned (pair._1 bs)))
                             (word.slu (combine n (pair._2 bs)) (word.of_Z 8))
  end.
Fixpoint split (n : nat) (w :word) : tuple byte n :=
  match n with
  | O => tt
  | S n => pair.mk (word.of_Z (word.unsigned w)) (split n (word.slu w (word.of_Z 8)))
  end.
Instance parameters : parameters :=
  let word := Word.Naive.word 64 (proj2 (Zlt_is_lt_bool 0 64) eq_refl) in
  let byte := Word.Naive.word 8 (proj2 (Zlt_is_lt_bool 0 8) eq_refl) in
  {|
  syntax := StringNamesSyntax.make BasicC64Syntax.StringNames_params;
  Semantics.word := word;
  word_zero := word.of_Z 0;
  word_succ := word.add (word.of_Z 1);
  word_test w := if word.eqb (word.of_Z 0) w then false else true;
  word_of_Z w := Some (word.of_Z w);
  interp_binop bop :=
    match bop with
    | bopname.add => word.add
    | bopname.sub => word.sub
    | bopname.mul => word.mul
    | bopname.and => word.and
    | bopname.or  => word.or
    | bopname.xor => word.xor
    | bopname.sru => word.sru
    | bopname.slu => word.slu
    | bopname.srs => word.srs
    | bopname.ltu => fun a b => if word.ltu a b then word.of_Z 1 else word.of_Z 0
    | bopname.lts => fun a b => if word.lts a b then word.of_Z 1 else word.of_Z 0
    | bopname.eq => fun a b => if word.eqb a b then word.of_Z 1 else word.of_Z 0
    end;
  (* TODO: bedrock2.Byte, bedrock2.Word8 *)
  Semantics.byte := byte;
  mem := SortedList.map (SortedList.parameters.Build_parameters word byte word.eqb word.ltu);
  Semantics.bytes_per := bytes_per;
  Semantics.combine sz := combine (bytes_per sz);
  Semantics.split sz := split (bytes_per sz);
  locals := SortedListString.map _;
  funname_eqb := String.eqb;
|}.
Existing Instance Word.Naive.ok.