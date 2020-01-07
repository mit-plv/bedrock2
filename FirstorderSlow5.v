(* -*- mode: coq; coq-prog-args: ("-emacs" "-R" "." "Top" "-top" "WPPInlined4M") -*- *)
(* File reduced by coq-bug-finder from original input, then from 5377 lines to 1273 lines, then from 1288 lines to 1137 lines *)
(* coqc version 8.12+alpha (December 2019) compiled on Dec 31 2019 9:59:24 with OCaml 4.09.0
   coqtop version samsdell:/home/sam/installs/coqmaster/coq,master (37254871c8e5ece576af7efddc20a9ed7f197e04) *)
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Require Coq.NArith.NArith.
Notation "'subst!' y 'for' x 'in' f" := (match y with x => f end) (at level 10).
Notation "'unique!' cls" := (ltac:(
  match constr:(Set) with
  | _ => let __ := constr:(_:cls) in fail 1 "unique!: already have an instance of" cls
  | _ => exact cls%type
  end))
  (at level 10, only parsing).
Global Unset Refine Instance Mode.
Module pair.
  Record pair {A B} := mk { _1 : A; _2 : B _1 }.
  Arguments pair : clear implicits.
  Arguments mk {A B} _ _.

  Notation "A * B" := (pair A%type (fun _ => B%type)) : type_scope.
End pair.
Module Export HList.
Import pair.
Local Set Universe Polymorphism.

Module Import polymorphic_list.
  Inductive list {A : Type} : Type := nil | cons (_:A) (_:list).
  Arguments list : clear implicits.

  Section WithA.
    Context {A : Type}.
    Fixpoint length (l : list A) : nat :=
      match l with
      | nil => 0
      | cons _ l' => S (length l')
      end.
  End WithA.

  Section WithElement.
    Context {A} (x : A).
    Fixpoint repeat (x : A) (n : nat) {struct n} : list A :=
      match n with
      | 0 => nil
      | S k => cons x (repeat x k)
      end.
  End WithElement.
End polymorphic_list.

Fixpoint hlist@{i j} (argts : list@{j} Type@{i}) : Type@{j} :=
  match argts with
  | nil => unit
  | cons T argts' => T * hlist argts'
  end.

Definition tuple A n := hlist (repeat A n).
Module Export tuple.
  Section WithA.
    Context {A : Type}.

    Fixpoint of_list (xs : list A) : tuple A (length xs) :=
      match xs with
      | nil => tt
      | cons x xs => pair.mk x (of_list xs)
      end.

    Fixpoint option_all {sz : nat} : tuple (option A) sz -> option (tuple A sz) :=
      match sz with
      | O => fun _ => Some tt
      | S sz' => fun '(pair.mk ox xs) =>
                   match ox, option_all xs with
                   | Some x, Some ys => Some (pair.mk x ys)
                   | _ , _ => None
                   end
      end.

    Section WithF.
      Context {B: Type}.
      Context (f: A -> B).
      Fixpoint map{sz: nat}: tuple A sz -> tuple B sz :=
        match sz with
        | O => fun _ => tt
        | S sz' => fun '(pair.mk x xs) => pair.mk (f x) (map xs)
        end.
    End WithF.

    Section WithStep.
      Context (step : A -> A).
      Fixpoint unfoldn (n : nat) (start : A) : tuple A n :=
        match n with
        | O => tt
        | S n => pair.mk start (unfoldn n (step start))
        end.
    End WithStep.
  End WithA.
End tuple.

End HList.
Definition autoforward (A B : Prop) := A -> B.
Import Coq.Arith.PeanoNat.
Import Coq.ZArith.BinInt.
Import Coq.NArith.NArith.

Hint Opaque Nat.ltb : typeclass_instances.

Existing Class BoolSpec.

Lemma BoolSpec_true P Q x (H : BoolSpec P Q x) : autoforward (x = true) P.
admit.
Defined.

Lemma BoolSpec_false P Q x (H : BoolSpec P Q x) : autoforward (x = false) Q.
admit.
Defined.

Hint Resolve BoolSpec_true BoolSpec_false : typeclass_instances.

Notation EqDecider f := (forall x y, BoolSpec (x = y) (x <> y) (f x y)).

Hint Resolve
     Nat.eqb_spec
     Nat.leb_spec
     Nat.ltb_spec
     N.eqb_spec
     N.leb_spec
     N.ltb_spec
     Z.eqb_spec
     Z.gtb_spec
     Z.geb_spec
     Z.leb_spec
     Z.ltb_spec
     String.eqb_spec
: typeclass_instances.
Import Coq.Lists.List.

Definition set(A: Type) := A -> Prop.

Definition elem_of{K: Type}(k: K)(ks: K -> Prop): Prop := ks k.

Notation "x '\in' s" := (elem_of x s) (at level 70, no associativity).

Section PropSet.
  Context {E: Type}.

  Definition empty_set: set E := fun _ => False.
  Definition singleton_set: E -> set E := eq.
  Definition union: set E -> set E -> set E :=
    fun s1 s2 x => x \in s1 \/ x \in s2.
  Definition intersect: set E -> set E -> set E :=
    fun s1 s2 x => x \in s1 /\ x \in s2.
  Definition diff: set E -> set E -> set E :=
    fun s1 s2 x => x \in s1 /\ ~ x \in s2.

  Definition add(s: set E)(e: E) := union (singleton_set e) s.
  Definition subset(s1 s2: set E) := forall x, x \in s1 -> x \in s2.
  Definition sameset(s1 s2: set E) := subset s1 s2 /\ subset s2 s1.
  Definition disjoint(s1 s2: set E) := forall x, (~ x \in s1) \/ (~ x \in s2).
  Definition of_option(o: option E) := match o with
                                       | Some e => singleton_set e
                                       | None => empty_set
                                       end.

End PropSet.

Hint Unfold
     elem_of
     empty_set
     singleton_set
     union
     intersect
     diff
     of_list
  : unf_basic_set_defs.

Hint Unfold
     add
     remove
     subset
     sameset
     disjoint
     of_option
  : unf_derived_set_defs.
Module Export Interface.

Module Export map.
  Class map {key value} := mk {
    rep : Type;

    get: rep -> key -> option value;

    empty : rep;
    put : rep -> key -> value -> rep;
    remove : rep -> key -> rep;
    putmany : rep -> rep -> rep;
  }.
  Arguments map : clear implicits.
  Global Coercion rep : map >-> Sortclass.

  Class ok {key value : Type} {map : map key value}: Prop := {
    map_ext : forall m1 m2, (forall k, get m1 k = get m2 k) -> m1 = m2;
    get_empty : forall k, get empty k = None;
    get_put_same : forall m k v, get (put m k v) k = Some v;
    get_put_diff : forall m k v k', k <> k' -> get (put m k' v) k = get m k;
    get_remove_same : forall m k, get (remove m k) k = None;
    get_remove_diff : forall m k k', k <> k' -> get (remove m k') k = get m k;
    get_putmany_left : forall m1 m2 k, get m2 k = None -> get (putmany m1 m2) k = get m1 k;
    get_putmany_right : forall m1 m2 k v, get m2 k = Some v -> get (putmany m1 m2) k = Some v;
  }.
  Arguments ok {_ _} _.

  Section WithMap.
    Context {key value : Type} {map : map key value} {map_ok : ok map}.
    Definition disjoint (a b : map) :=
      forall k v1 v2, get a k = Some v1 -> get b k = Some v2 -> False.
    Definition sub_domain(m1 m2: map): Prop :=
      forall k v1, map.get m1 k = Some v1 -> exists v2, map.get m2 k = Some v2.
    Definition same_domain(m1 m2: map): Prop := sub_domain m1 m2 /\ sub_domain m2 m1.
    Definition split m m1 m2 := m = (putmany m1 m2) /\ disjoint m1 m2.

    Fixpoint putmany_of_list_zip (keys : list key) (values : list value) (init : rep) {struct keys} : option map :=
      match keys, values with
      | nil, nil => Some init
      | cons k keys, cons v values =>
        putmany_of_list_zip keys values (put init k v)
      | _, _ => None
      end.

    Definition getmany_of_tuple(m: map){sz: nat}(keys: tuple key sz): option (tuple value sz) :=
      tuple.option_all (tuple.map (get m) keys).

    Fixpoint putmany_of_tuple {sz : nat} : tuple key sz -> tuple value sz -> map -> map :=
      match sz with
      | O => fun keys values init => init
      | S sz' => fun '(pair.mk k ks) '(pair.mk v vs) init =>
                   put (putmany_of_tuple ks vs init) k v
      end.
  End WithMap.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

Module Export Z.

  Lemma testbit_minus1 i (H:0<=i) :
    Z.testbit (-1) i = true.
admit.
Defined.

  Lemma shiftl_spec': forall a n m : Z,
      Z.testbit (Z.shiftl a n) m = negb (m <? 0) && Z.testbit a (m - n).
admit.
Defined.

  Lemma shiftr_spec': forall a n m : Z,
      Z.testbit (Z.shiftr a n) m = negb (m <? 0) && Z.testbit a (m + n).
admit.
Defined.

  Lemma lnot_spec' : forall a n : Z,
      Z.testbit (Z.lnot a) n = negb (n <? 0) && negb (Z.testbit a n).
admit.
Defined.

  Lemma div_pow2_bits' : forall a n m : Z,
      0 <= n ->
      Z.testbit (a / 2 ^ n) m = negb (m <? 0) && Z.testbit a (m + n).
admit.
Defined.

  Lemma bits_opp' : forall a n : Z,
      Z.testbit (- a) n = negb (n <? 0) && negb (Z.testbit (Z.pred a) n).
admit.
Defined.

  Lemma testbit_ones_nonneg' : forall n i : Z,
      0 <= n ->
      Z.testbit (Z.ones n) i = negb (i <? 0) && (i <? n).
admit.
Defined.

  Lemma testbit_minus1' : forall i : Z,
      Z.testbit (-1) i = negb (i <? 0).
admit.
Defined.

  Hint Rewrite
       Z.lor_spec
       Z.lxor_spec
       Z.land_spec
       Z.ldiff_spec
       Z.testbit_0_l
    : z_bitwise_no_hyps.
  Hint Rewrite <-Z.ones_equiv : z_bitwise_no_hyps.

  Hint Rewrite
       Z.shiftl_spec_low
       Z.shiftl_spec_alt
       Z.shiftl_spec
       Z.shiftr_spec_aux
       Z.lnot_spec
       Z.shiftr_spec
       Z.ones_spec_high
       Z.ones_spec_low
       Z.div_pow2_bits
       Z.pow2_bits_eqb
       Z.bits_opp
       Z.testbit_mod_pow2
       Z.testbit_ones_nonneg
       Z.testbit_minus1
       using solve [auto with zarith]
    : z_bitwise_with_hyps.

  Hint Rewrite
       Z.shiftl_spec'
       Z.shiftr_spec'
       Z.lnot_spec'
       Z.div_pow2_bits'
       Z.bits_opp'
       Z.testbit_ones_nonneg'
       Z.testbit_minus1'
       using solve [auto with zarith]
    : z_bitwise_forced_no_hyps.

Module Export coqutil_DOT_Word_DOT_Interface.
Module Export coqutil.
Module Export Word.
Module Interface.

Module Export word.
  Class word {width : Z} := {
    rep : Type;

    unsigned : rep -> Z;
    signed : rep -> Z;
    of_Z : Z -> rep;

    add : rep -> rep -> rep;
    sub : rep -> rep -> rep;
    opp : rep -> rep;

    or : rep -> rep -> rep;
    and : rep -> rep -> rep;
    xor : rep -> rep -> rep;
    not : rep -> rep;
    ndn : rep -> rep -> rep;

    mul : rep -> rep -> rep;
    mulhss : rep -> rep -> rep;
    mulhsu : rep -> rep -> rep;
    mulhuu : rep -> rep -> rep;

    divu : rep -> rep -> rep;
    divs : rep -> rep -> rep;
    modu : rep -> rep -> rep;
    mods : rep -> rep -> rep;

    slu : rep -> rep -> rep;
    sru : rep -> rep -> rep;
    srs : rep -> rep -> rep;

    eqb : rep -> rep -> bool;
    ltu : rep -> rep -> bool;
    lts : rep -> rep -> bool;

    gtu x y := ltu y x;
    gts x y := lts y x;

    swrap z := (z + 2^(width-1)) mod 2^width - 2^(width-1);

    sextend: Z -> rep -> rep;
  }.
  Arguments word : clear implicits.

  Class ok {width} {word : word width}: Prop := {
    wrap z := z mod 2^width;

    width_pos: 0 < width;

    unsigned_of_Z : forall z, unsigned (of_Z z) = wrap z;
    signed_of_Z : forall z, signed (of_Z z) = swrap z;
    of_Z_unsigned : forall x, of_Z (unsigned x) = x;

    unsigned_add : forall x y, unsigned (add x y) = wrap (Z.add (unsigned x) (unsigned y));
    unsigned_sub : forall x y, unsigned (sub x y) = wrap (Z.sub (unsigned x) (unsigned y));
    unsigned_opp : forall x, unsigned (opp x) = wrap (Z.opp (unsigned x));

    unsigned_or : forall x y, unsigned (or x y) = wrap (Z.lor (unsigned x) (unsigned y));
    unsigned_and : forall x y, unsigned (and x y) = wrap (Z.land (unsigned x) (unsigned y));
    unsigned_xor : forall x y, unsigned (xor x y) = wrap (Z.lxor (unsigned x) (unsigned y));
    unsigned_not : forall x, unsigned (not x) = wrap (Z.lnot (unsigned x));
    unsigned_ndn : forall x y, unsigned (ndn x y) = wrap (Z.ldiff (unsigned x) (unsigned y));

    unsigned_mul : forall x y, unsigned (mul x y) = wrap (Z.mul (unsigned x) (unsigned y));
    signed_mulhss : forall x y, signed (mulhss x y) = swrap (Z.mul (signed x) (signed y) / 2^width);
    signed_mulhsu : forall x y, signed (mulhsu x y) = swrap (Z.mul (signed x) (unsigned y) / 2^width);
    unsigned_mulhuu : forall x y, unsigned (mulhuu x y) = wrap (Z.mul (unsigned x) (unsigned y) / 2^width);

    unsigned_divu : forall x y, unsigned y <> 0 -> unsigned (divu x y) = wrap (Z.div (unsigned x) (unsigned y));
    signed_divs : forall x y, signed y <> 0 -> signed x <> -2^(width-1) \/ signed y <> -1 -> signed (divs x y) = swrap (Z.quot (signed x) (signed y));
    unsigned_modu : forall x y, unsigned y <> 0 -> unsigned (modu x y) = wrap (Z.modulo (unsigned x) (unsigned y));
    signed_mods : forall x y, signed y <> 0 -> signed (mods x y) = swrap (Z.rem (signed x) (signed y));

    unsigned_slu : forall x y, Z.lt (unsigned y) width -> unsigned (slu x y) = wrap (Z.shiftl (unsigned x) (unsigned y));
    unsigned_sru : forall x y, Z.lt (unsigned y) width -> unsigned (sru x y) = wrap (Z.shiftr (unsigned x) (unsigned y));
    signed_srs : forall x y, Z.lt (unsigned y) width -> signed (srs x y) = swrap (Z.shiftr (signed x) (unsigned y));

    unsigned_eqb : forall x y, eqb x y = Z.eqb (unsigned x) (unsigned y);
    unsigned_ltu : forall x y, ltu x y = Z.ltb (unsigned x) (unsigned y);
    signed_lts : forall x y, lts x y = Z.ltb (signed x) (signed y);
  }.
  Arguments ok {_} _.
End word.
Notation word := word.word.
Global Coercion word.rep : word >-> Sortclass.

End Interface.
Module Export Properties.
Import coqutil_DOT_Word_DOT_Interface.coqutil.Word.Interface.

Module Export word.
  Section WithWord.
    Context {width} {word : word width} {word_ok : word.ok word}.

    Hint Rewrite
       unsigned_of_Z signed_of_Z of_Z_unsigned unsigned_add unsigned_sub unsigned_opp unsigned_or unsigned_and unsigned_xor unsigned_not unsigned_ndn unsigned_mul signed_mulhss signed_mulhsu unsigned_mulhuu unsigned_divu signed_divs unsigned_modu signed_mods unsigned_slu unsigned_sru signed_srs unsigned_eqb unsigned_ltu signed_lts
       using trivial
  : word_laws.

    Lemma ring_theory : Ring_theory.ring_theory (of_Z 0) (of_Z 1) add mul sub opp Logic.eq.
admit.
Defined.
    Lemma ring_morph_add : forall x y : Z, of_Z (x + y) = add (of_Z x) (of_Z y).
admit.
Defined.
    Lemma ring_morph_sub : forall x y : Z, of_Z (x - y) = sub (of_Z x) (of_Z y).
admit.
Defined.
    Lemma ring_morph_mul : forall x y : Z, of_Z (x * y) = mul (of_Z x) (of_Z y).
admit.
Defined.
    Lemma ring_morph_opp : forall x : Z, of_Z (- x) = opp (of_Z x).
admit.
Defined.
    Lemma ring_morph :
      Ring_theory.ring_morph (of_Z 0) (of_Z 1) add   mul   sub   opp   Logic.eq
                             0        1        Z.add Z.mul Z.sub Z.opp Zbool.Zeq_bool of_Z.
admit.
Defined.

    Lemma testbit_wrap z i : Z.testbit (wrap z) i = ((i <? width) && Z.testbit z i)%bool.
admit.
Defined.

    Lemma eqb_spec(a b: word): BoolSpec (a = b) (a <> b) (word.eqb a b).
admit.
Defined.

    Lemma testbit_swrap z i : Z.testbit (swrap z) i
                              = if i <? width
                                then Z.testbit (wrap z) i
                                else Z.testbit (wrap z) (width -1).
admit.
Defined.

    Lemma testbit_signed x i : Z.testbit (signed x) i
                               = if i <? width
                                 then Z.testbit (unsigned x) i
                                 else Z.testbit (unsigned x) (width -1).
admit.
Defined.

    Hint Rewrite testbit_signed testbit_wrap testbit_swrap
         using solve [auto with zarith] : z_bitwise_signed.
  End WithWord.

  End word.

Existing Instance word.eqb_spec.

Ltac word_cst w :=
  match w with
  | word.of_Z ?x => let b := isZcst x in
                    match b with
                    | true => x
                    | _ => constr:(NotConstant)
                    end
  | _ => constr:(NotConstant)
  end.

Hint Rewrite
  @word.ring_morph_add
  @word.ring_morph_sub
  @word.ring_morph_mul
  @word.ring_morph_opp
  using typeclasses eauto
  : rew_word_morphism.

Section RingDemoAndTest.

  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  Goal False.
    assert (forall (w1 w2: word), word.add w1 w2 = word.add w2 w1) as A.
    {
 intros.
ring.
}
 clear A.

    assert (forall (z: Z) (w: word),
               word.add w (word.mul (word.of_Z 4)
                                    (word.sub (word.of_Z (1 + z + 1)) (word.of_Z z))) =
               word.add (word.add w (word.of_Z 4)) (word.of_Z 4)) as A.
    {
 intros.
ring.
}
 clear A.

    assert (forall (L : Z) (w : word),
               word.add w (word.of_Z ((L + 2) * 4)) =
               word.add (word.add (word.add w (word.of_Z 4))
                                  (word.mul (word.of_Z 4) (word.of_Z L)))
                        (word.of_Z 4)) as A.
    {
 intros.
ring.
}
 clear A.
  Abort.

  Goal False.
    assert (forall (w1 w2 w3: word),
               word.sub (word.add w1 w2) (word.add w2 w3) =
               word.sub w1 w3) as A.
    {
 intros.
ring_simplify (sub (add w1 w2) (add w2 w3)).
reflexivity.
}
 clear A.
  Abort.

End RingDemoAndTest.

End Properties.

Notation "'bind_ex' x <- a ; f" :=
  (subst! a for a' in exists x, a' x /\ f)
  (only parsing, right associativity, at level 60, f at level 200).
Notation "'bind_ex_Some' x <- a ; f" :=
  (subst! a for a' in exists x, a' = Some x /\ f)
  (only parsing, right associativity, at level 60, f at level 200).
Module Export dlet.
Definition dlet {A P} (x : A) (f : forall a : A, P a) : P x
  := let y := x in f y.
Notation "'dlet!' x .. y := v 'in' f" :=
  (dlet v (fun x => .. (fun y => f) .. ))
    (at level 200, x binder, y binder, f at level 200,
     format "'dlet!'  x .. y  :=  v  'in' '//' f").

Module Export bedrock2_DOT_Syntax.
Module Export bedrock2.
Module Export Syntax.

Module Import bopname.
  Inductive bopname := add | sub | mul | mulhuu | divu | remu | and | or | xor | sru | slu | srs | lts | ltu | eq.
End bopname.
Notation bopname := bopname.bopname.

Class parameters := {
  varname : Type;
  funname : Type;
  actname : Type;
}.

Module Export access_size.
  Variant access_size := one | two | four | word.
End access_size.

Module expr.
Section expr.
  Context {p : unique! parameters}.
  Inductive expr  : Type :=
  | literal (v: Z)
  | var (x: varname)
  | load (_ : access_size) (addr:expr)
  | op (op: bopname) (e1 e2: expr).
End expr.
End expr.
Notation expr := expr.expr.

Module Export cmd.
Section cmd.
  Context {p : unique! parameters}.
  Inductive cmd :=
  | skip
  | set (lhs : varname) (rhs : expr)
  | unset (lhs : varname)
  | store (_ : access_size) (address : expr) (value : expr)
  | cond (condition : expr) (nonzero_branch zero_branch : cmd)
  | seq (s1 s2: cmd)
  | while (test : expr) (body : cmd)
  | call (binds : list varname) (function : funname) (args: list expr)
  | interact (binds : list varname) (action : actname) (args: list expr).
End cmd.
End cmd.

End Syntax.

End bedrock2.

End bedrock2_DOT_Syntax.
Module Export LittleEndian.
Import coqutil_DOT_Word_DOT_Interface.coqutil.Word.Interface.

Section LittleEndian.
  Context {byte: word 8}.

  Fixpoint combine (n : nat) : forall (bs : tuple byte n), Z :=
    match n with
    | O => fun _ => 0
    | S n => fun bs => Z.lor (word.unsigned (pair._1 bs))
                             (Z.shiftl (combine n (pair._2 bs)) 8)
    end.

  Fixpoint split (n : nat) (w : Z) : tuple byte n :=
    match n with
    | O => tt
    | S n => pair.mk (word.of_Z w) (split n (Z.shiftr w 8))
    end.

End LittleEndian.

End LittleEndian.

Module Export bedrock2_DOT_MetricLogging.
Module Export bedrock2.
Module Export MetricLogging.

Section Riscv.

  Record MetricLog := mkMetricLog {
    instructions: Z;
    stores: Z;
    loads: Z;
    jumps: Z;
  }.

  Definition withInstructions i log := mkMetricLog i (stores log) (loads log) (jumps log).
  Definition withStores s log := mkMetricLog (instructions log) s (loads log) (jumps log).
  Definition withLoads l log := mkMetricLog (instructions log) (stores log) l (jumps log).
  Definition withJumps j log := mkMetricLog (instructions log) (stores log) (loads log) j.

  Definition addMetricInstructions n log := withInstructions (instructions log + n) log.
  Definition addMetricStores n log := withStores (stores log + n) log.
  Definition addMetricLoads n log := withLoads (loads log + n) log.
  Definition addMetricJumps n log := withJumps (jumps log + n) log.

  Definition subMetricInstructions n log := withInstructions (instructions log - n) log.
  Definition subMetricStores n log := withStores (stores log - n) log.
  Definition subMetricLoads n log := withLoads (loads log - n) log.
  Definition subMetricJumps n log := withJumps (jumps log - n) log.

  Definition metricSub(metric: MetricLog -> Z) finalM initialM : Z :=
    Z.sub (metric finalM) (metric initialM).

  Definition metricsOp op : MetricLog -> MetricLog -> MetricLog :=
    fun initialM finalM =>
      mkMetricLog
        (op instructions initialM finalM)
        (op stores initialM finalM)
        (op loads initialM finalM)
        (op jumps initialM finalM).

  Definition metricsSub := metricsOp metricSub.

  Definition metricLeq(metric: MetricLog -> Z) m1 m2: Prop :=
    (metric m1) <= (metric m2).

  Definition metricsLeq(m1: MetricLog)(m2: MetricLog): Prop :=
    metricLeq instructions m1 m2 /\
    metricLeq stores m1 m2 /\
    metricLeq loads m1 m2 /\
    metricLeq jumps m1 m2.

End Riscv.

Hint Unfold
     withInstructions
     withLoads
     withStores
     withJumps
     addMetricInstructions
     addMetricLoads
     addMetricStores
     addMetricJumps
     subMetricInstructions
     subMetricLoads
     subMetricStores
     subMetricJumps
     metricsOp
     metricSub
     metricsSub
     metricLeq
     metricsLeq
  : unf_metric_log.

End MetricLogging.

End bedrock2.

End bedrock2_DOT_MetricLogging.

Section WithMap.
    Hint Resolve
         get_empty
         get_remove_same
         get_remove_diff
         get_put_same
         get_put_diff
         get_putmany_left
         get_putmany_right
      : map_spec_hints_separate.
  End WithMap.

Module Export bedrock2_DOT_Memory.
Module Export bedrock2.
Module Export Memory.
Import coqutil_DOT_Word_DOT_Interface.coqutil.Word.Interface.

Section Memory.
  Context {byte: word 8} {width: Z} {word: word width} {mem: map.map word byte}.

  Definition footprint(a: word)(sz: nat): tuple word sz :=
    tuple.unfoldn (fun w => word.add w (word.of_Z 1)) sz a.

  Definition load_bytes(sz: nat)(m: mem)(addr: word): option (tuple byte sz) :=
    map.getmany_of_tuple m (footprint addr sz).

  Definition unchecked_store_bytes(sz: nat)(m: mem)(a: word)(bs: tuple byte sz): mem :=
    map.putmany_of_tuple (footprint a sz) bs m.

  Definition store_bytes(sz: nat)(m: mem)(a: word)(v: tuple byte sz): option mem :=
    match load_bytes sz m a with
    | Some _ => Some (unchecked_store_bytes sz m a v)
    | None => None
    end.

  Definition bytes_per sz :=
    match sz with
      | access_size.one => 1 | access_size.two => 2 | access_size.four => 4
      | access_size.word => Z.to_nat (Z.div (Z.add width 7) 8)
    end%nat.

  Definition load_Z(sz: access_size)(m: mem)(a: word): option Z :=
    match load_bytes (bytes_per sz) m a with
    | Some bs => Some (LittleEndian.combine _ bs)
    | None => None
    end.

  Definition store_Z(sz: access_size)(m: mem)(a: word)(v: Z): option mem :=
    store_bytes (bytes_per sz) m a (LittleEndian.split _ v).

  Definition load(sz: access_size)(m: mem)(a: word): option word :=
    match load_Z sz m a with
    | Some v => Some (word.of_Z v)
    | None => None
    end.

  Definition store(sz: access_size)(m: mem)(a: word)(v: word): option mem :=
    store_Z sz m a (word.unsigned v).

End Memory.

End Memory.

End bedrock2.

End bedrock2_DOT_Memory.

Module Export bedrock2_DOT_Semantics.
Module Export bedrock2.
Module Export Semantics.
Import coqutil_DOT_Word_DOT_Interface.coqutil.Word.Interface.

Class parameters := {
  syntax :> Syntax.parameters;
  varname_eqb: varname -> varname -> bool;
  funname_eqb: funname -> funname -> bool;
  actname_eqb: actname -> actname -> bool;

  width : Z;
  word :> Word.Interface.word width;
  byte :> Word.Interface.word 8%Z;

  mem :> map.map word byte;
  locals :> map.map varname word;
  funname_env : forall T: Type, map.map funname T;

  trace := list ((mem * actname * list word) * (mem * list word));

  ExtSpec :=

    trace -> mem -> actname -> list word ->

    (mem -> list word -> Prop) ->

    Prop;

  ext_spec: ExtSpec;
}.

Module Export ext_spec.
  Class ok{p: parameters}: Prop := {

    unique_mGive_footprint: forall t1 t2 mGive1 mGive2 a args
                                            (post1 post2: mem -> list word -> Prop),
        ext_spec t1 mGive1 a args post1 ->
        ext_spec t2 mGive2 a args post2 ->
        map.same_domain mGive1 mGive2;

    weaken :> forall t mGive act args,
        Morphisms.Proper
          (Morphisms.respectful
             (Morphisms.pointwise_relation Interface.map.rep
               (Morphisms.pointwise_relation (list word) Basics.impl)) Basics.impl)
          (ext_spec t mGive act args);

    intersect: forall t mGive a args
                      (post1 post2: mem -> list word -> Prop),
        ext_spec t mGive a args post1 ->
        ext_spec t mGive a args post2 ->
        ext_spec t mGive a args (fun mReceive resvals =>
                                   post1 mReceive resvals /\ post2 mReceive resvals);
  }.
End ext_spec.
Arguments ext_spec.ok: clear implicits.

Class parameters_ok{p: parameters}: Prop := {
  varname_eqb_spec :> EqDecider varname_eqb;
  funname_eqb_spec :> EqDecider funname_eqb;
  actname_eqb_spec :> EqDecider actname_eqb;
  width_cases : width = 32 \/ width = 64;
  word_ok :> word.ok word;
  byte_ok :> word.ok byte;
  mem_ok :> map.ok mem;
  locals_ok :> map.ok locals;
  funname_env_ok : forall T: Type, map.ok (funname_env T);
  ext_spec_ok :> ext_spec.ok p;
}.
Arguments parameters_ok: clear implicits.

Instance env{p: parameters}: map.map funname (list varname * list varname * cmd) :=
  funname_env _.

Section binops.
  Context {width : Z} {word : Word.Interface.word width}.
  Definition interp_binop (bop : bopname) : word -> word -> word :=
    match bop with
    | bopname.add => word.add
    | bopname.sub => word.sub
    | bopname.mul => word.mul
    | bopname.mulhuu => word.mulhuu
    | bopname.divu => word.divu
    | bopname.remu => word.modu
    | bopname.and => word.and
    | bopname.or => word.or
    | bopname.xor => word.xor
    | bopname.sru => word.sru
    | bopname.slu => word.slu
    | bopname.srs => word.srs
    | bopname.lts => fun a b =>
      if word.lts a b then word.of_Z 1 else word.of_Z 0
    | bopname.ltu => fun a b =>
      if word.ltu a b then word.of_Z 1 else word.of_Z 0
    | bopname.eq => fun a b =>
      if word.eqb a b then word.of_Z 1 else word.of_Z 0
    end.
End binops.

End Semantics.

End bedrock2.

End bedrock2_DOT_Semantics.
Module Export bedrock2.
Module Export WeakestPrecondition.
Import coqutil_DOT_Word_DOT_Interface.coqutil.Word.Interface.
Import bedrock2_DOT_Semantics.bedrock2.Semantics.

Section WeakestPrecondition.
  Context {p : unique! Semantics.parameters}.

  Definition literal v (post : word -> Prop) : Prop :=
    dlet! v := word.of_Z v in post v.
  Definition get (l : locals) (x : varname) (post : word -> Prop) : Prop :=
    bind_ex_Some v <- map.get l x; post v.
  Definition load s m a (post : _ -> Prop) : Prop :=
    bind_ex_Some v <- load s m a; post v.
  Definition store sz m a v post :=
    bind_ex_Some m <- store sz m a v; post m.

  Section WithMemAndLocals.
    Context (m : mem) (l : locals).
    Definition expr_body rec (e : Syntax.expr) (post : word -> Prop) : Prop :=
      match e with
      | expr.literal v =>
        literal v post
      | expr.var x =>
        get l x post
      | expr.op op e1 e2 =>
        rec e1 (fun v1 =>
        rec e2 (fun v2 =>
        post (interp_binop op v1 v2)))
      | expr.load s e =>
        rec e (fun a =>
        load s m a post)
    end.
    Fixpoint expr e := expr_body expr e.
  End WithMemAndLocals.

  Section WithF.
    Context {A B} (f: A -> (B -> Prop) -> Prop).
    Definition list_map_body rec (xs : list A) (post : list B -> Prop) : Prop :=
      match xs with
      | nil => post nil
      | cons x xs' =>
        f x (fun y =>
        rec xs' (fun ys' =>
        post (cons y ys')))
      end.
    Fixpoint list_map xs := list_map_body list_map xs.
  End WithF.

  Section WithFunctions.
    Context (call : funname -> trace -> mem -> list word -> (trace -> mem -> list word -> Prop) -> Prop).
    Definition dexpr m l e v := expr m l e (eq v).
    Definition dexprs m l es vs := list_map (expr m l) es (eq vs).
    Definition cmd_body (rec:_->_->_->_->_->Prop) (c : cmd) (t : trace) (m : mem) (l : locals)
             (post : trace -> mem -> locals -> Prop) : Prop :=

      match c with
      | cmd.skip => post t m l
      | cmd.set x ev =>
        bind_ex v <- dexpr m l ev;
        dlet! l := map.put l x v in
        post t m l
      | cmd.unset x =>
        dlet! l := map.remove l x in
        post t m l
      | cmd.store sz ea ev =>
        bind_ex a <- dexpr m l ea;
        bind_ex v <- dexpr m l ev;
        store sz m a v (fun m =>
        post t m l)
      | cmd.cond br ct cf =>
        bind_ex v <- dexpr m l br;
        (word.unsigned v <> 0%Z -> rec ct t m l post) /\
        (word.unsigned v = 0%Z -> rec cf t m l post)
      | cmd.seq c1 c2 =>
        rec c1 t m l (fun t m l => rec c2 t m l post)
      | cmd.while e c =>
        exists measure (lt:measure->measure->Prop) (inv:measure->trace->mem->locals->Prop),
        Coq.Init.Wf.well_founded lt /\
        (exists v, inv v t m l) /\
        (forall v t m l, inv v t m l ->
          bind_ex b <- dexpr m l e;
          (word.unsigned b <> 0%Z -> rec c t m l (fun t' m l =>
            exists v', inv v' t' m l /\ lt v' v)) /\
          (word.unsigned b = 0%Z -> post t m l))
      | cmd.call binds fname arges =>
        bind_ex args <- dexprs m l arges;
        call fname t m args (fun t m rets =>
          bind_ex_Some l <- map.putmany_of_list_zip binds rets l;
          post t m l)
      | cmd.interact binds action arges =>
        bind_ex args <- dexprs m l arges;
        exists mKeep mGive, map.split m mKeep mGive /\
        ext_spec t mGive action args (fun mReceive rets =>
          bind_ex_Some l <- map.putmany_of_list_zip binds rets l;
          exists m, map.split m mKeep mReceive /\
          post (cons ((mGive, action, args), (mReceive, rets)) t) m l)
      end.
    Fixpoint cmd c := cmd_body cmd c.
  End WithFunctions.
End WeakestPrecondition.

End WeakestPrecondition.

End bedrock2.
Import Coq.Classes.Morphisms.

Section WeakestPrecondition.
  Context {p : unique! Semantics.parameters}.

  Ltac ind_on X :=
    intros;
    repeat match goal with x : ?T |- _ => first [ constr_eq T X; move x at top | revert x ] end;
    match goal with x : X |- _ => induction x end;
    intros.

  Global Instance Proper_literal : Proper (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl)) WeakestPrecondition.literal.
admit.
Defined.

  Global Instance Proper_get : Proper (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl))) WeakestPrecondition.get.
admit.
Defined.

  Global Instance Proper_load : Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl)))) WeakestPrecondition.load.
admit.
Defined.

  Global Instance Proper_store : Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl))))) WeakestPrecondition.store.
admit.
Defined.

  Global Instance Proper_expr : Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl)))) WeakestPrecondition.expr.
admit.
Defined.

  Global Instance Proper_list_map {A B} :
    Proper ((pointwise_relation _ (pointwise_relation _ Basics.impl ==> Basics.impl)) ==> pointwise_relation _ (pointwise_relation _ Basics.impl ==> Basics.impl)) (WeakestPrecondition.list_map (A:=A) (B:=B)).
admit.
Defined.

  Context {p_ok : Semantics.parameters_ok p}.
  Global Instance Proper_cmd :
    Proper (
     (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ (pointwise_relation _ Basics.impl))) ==> Basics.impl)))) ==>
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ Basics.impl))) ==>
     Basics.impl)))))) WeakestPrecondition.cmd.
  Proof.
    cbv [Proper respectful pointwise_relation Basics.flip Basics.impl]; ind_on Syntax.cmd.cmd;
      cbn in *; cbv [dlet.dlet] in *; intuition (try typeclasses eauto with core).
    {
 destruct H1 as (?&?&?).
eexists.
split.
      1: eapply Proper_expr.
      1: cbv [pointwise_relation Basics.impl]; intuition eauto 2.
      all: eauto.
}
    {
 destruct H1 as (?&?&?).
eexists.
split.
      {
 eapply Proper_expr.
        {
 cbv [pointwise_relation Basics.impl]; intuition eauto 2.
}
        {
 eauto.
}
 }
      {
 destruct H2 as (?&?&?).
eexists.
split.
        {
 eapply Proper_expr.
          {
 cbv [pointwise_relation Basics.impl]; intuition eauto 2.
}
          {
 eauto.
}
 }
        {
 eapply Proper_store; eauto; cbv [pointwise_relation Basics.impl]; eauto.
}
 }
 }
    {
 destruct H1 as (?&?&?).
eexists.
split.
      {
 eapply Proper_expr.
        {
 cbv [pointwise_relation Basics.impl]; intuition eauto 2.
}
        {
 eauto.
}
 }
      {
 intuition eauto 6.
}
 }
    {
 destruct H1 as (?&?&?&?&?&HH).
      eassumption || eexists.
      eassumption || eexists.
      eassumption || eexists.
      eassumption || eexists.
{
 eassumption || eexists.
}
      eassumption || eexists.
{
 eassumption || eexists.
}
      intros X Y Z T W.
      specialize (HH X Y Z T W).
      destruct HH as (?&?&?).
eexists.
split.
      1: eapply Proper_expr.
      1: cbv [pointwise_relation Basics.impl].
      all:intuition eauto 2.
      -
 eapply H2; eauto; cbn; intros.
        match goal with H:_ |- _ => destruct H as (?&?&?); solve[eauto] end.
      -
 intuition eauto.
}
    {
 destruct H1 as (?&?&?).
eexists.
split.
      {
 eapply Proper_list_map; eauto; try exact H4; cbv [respectful pointwise_relation Basics.impl]; intuition eauto 2.
        eapply Proper_expr; eauto.
}
      {
 eapply H; eauto.
Timeout 10 firstorder eauto.

