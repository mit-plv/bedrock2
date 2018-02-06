Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.
Require Import lib.LibTacticsMin.

(* Note: you can't ask an array for its length *)
Class IsArray(T E: Type) := mkIsArray {
  defaultElem: E;
  get: T -> nat -> E;
  update: T -> nat -> E -> T;
  newArray: nat -> T
}.

Definition listUpdate{E: Type}(l: list E)(i: nat)(e: E): list E :=
  firstn i l ++ [e] ++ skipn (S i) l.

Definition listFill{E: Type}(e: E): nat -> list E :=
  fix rec(n: nat) := match n with
  | O => nil
  | S m => e :: rec m
  end.

Instance ListIsArray: forall (T: Type) (d: T), IsArray (list T) T := fun T d => {|
  defaultElem := d;
  get := fun l i => nth i l d;
  update := listUpdate;
  newArray := listFill d
|}.

Notation "'for' m 'from' 0 'to' N 'updating' ( s1 ) {{ b }} ;; rest" :=
  (let s1 :=
    (fix rec(n: nat) := match n with
     | 0 => s1
     | S m => let s1 := rec m in b
     end) N
  in rest)
  (at level 20, right associativity).

Notation "'for' m 'from' 0 'to' N 'updating' ( s1 ',' s2 ) {{ b }} ;; rest" :=
  (let '(s1, s2) :=
    (fix rec(n: nat) := match n with
     | 0 => (s1, s2)
     | S m =>
         let '(s1, s2) := rec m in b
     end) N
  in rest)
  (at level 20, right associativity).

Notation "'for' m 'from' 0 'to' N 'updating' ( s1 , s2 , s3 ) {{ b }} ;; rest" :=
  (let '(s1, s2, s3) :=
    (fix rec(n: nat) := match n with
     | 0 => (s1, s2, s3)
     | S m =>
         let '(s1, s2, s3) := rec m in b
     end) N
  in rest)
  (at level 20, right associativity).

Notation "'for' m 'from' 0 'to' N 'updating' ( s1 , s2 , s3 , s4 ) {{ b }} ;; rest" :=
  (let '(s1, s2, s3, s4) :=
    (fix rec(n: nat) := match n with
     | 0 => (s1, s2, s3, s4)
     | S m =>
         let '(s1, s2, s3, s4) := rec m in b
     end) N
  in rest)
  (at level 20, right associativity).

Notation "'for' m 'from' 0 'to' N 'updating' ( s1 , s2 , s3 , s4 , s5 ) {{ b }} ;; rest" :=
  (let '(s1, s2, s3, s4, s5) :=
    (fix rec(n: nat) := match n with
     | 0 => (s1, s2, s3, s4, s5)
     | S m =>
         let '(s1, s2, s3, s4, s5) := rec m in b
     end) N
  in rest)
  (at level 20, right associativity).

Section toposort.
  Context {Array: Set -> Set}.
  (*Context {ArrayIsArray: forall (E: Set), IsArray (Array E) E}.*)
  Context {NatArrayIsArray: IsArray (Array nat) nat}.
  Context {NatArrayArrayIsArray: IsArray (Array (Array nat)) (Array nat)}.

  Definition increment(a: Array nat)(i: nat): Array nat :=
    update a i (S (get a i)).

  Definition decrement(a: Array nat)(i: nat): Array nat :=
    update a i (pred (get a i)).

  Definition toposort
    (N: nat) (* number of nodes *)
    (A: Array (Array nat)) (* adjacency list for each node *)
    (outDegs: Array nat) (* out-degrees; outDegs[i] = length of A[i] *)
  : Array nat (* returns topologically sorted list *) :=
  let todo := newArray N in
  let todoSize := 0 in
  let inDegs := newArray N in
  for i from 0 to N updating (inDegs) {{
    update inDegs i 0
  }} ;;
  for i from 0 to N updating (inDegs) {{
    for j from 0 to (get outDegs i) updating (inDegs) {{
      increment inDegs (get (get A i) j)
    }} ;;
    inDegs
  }} ;;
  for i from 0 to N updating (todoSize, todo) {{ 
     if get inDegs i =? 0 then
      let todo := update todo todoSize i in
      let todoSize := S todoSize in
      (todoSize, todo)
    else
      (todoSize, todo)
  }} ;;
  let res := newArray N in
  for resSize from 0 to N updating (todoSize, todo, res, inDegs) {{
    let todoSize := pred todoSize in
    let n := get todo todoSize in
    let res := update res resSize n in
    for j from 0 to (get outDegs n) updating (todoSize, todo, inDegs) {{
      let inDegs := decrement inDegs (get (get A n) j) in
      if get inDegs (get (get A n) j) =? 0 then
        let todo := update todo todoSize (get (get A n) j) in
        let todoSize := S todoSize in
        (todoSize, todo, inDegs)
      else
        (todoSize, todo, inDegs)
    }} ;;
    (todoSize, todo, res, inDegs)
  }} ;;
  res.



(*




  Definition toposort
    (N: nat) (* number of nodes *)
    (A: Array (Array nat)) (* adjacency list for each node *)
    (outDegs: Array nat) (* out-degrees; outDegs[i] = length of A[i] *)
  : Array nat (* returns topologically sorted list *) :=
  let todo := newArray N in
  let todoSize := 0 in
  let inDegs := newArray N in
  let inDegs := forLoop inDegs N (fun i inDegs =>
    update inDegs i 0
  ) in
  let inDegs := forLoop inDegs N (fun i inDegs =>
    forLoop inDegs (get outDegs i) (fun j inDegs =>
      increment inDegs (get (get A i) j)
    )
  ) in
  let '(_, todoSize, todo) := forLoop (tt, todoSize, todo) N (fun i p =>
    let '(_, todoSize, todo) := p in
    let '(_, todoSize, todo) :=
    if get inDegs i =? 0 then
      let todo := update todo todoSize i in
      let todoSize := S todoSize in
      (tt, todoSize, todo)
    else
      (tt, todoSize, todo)
    in (tt, todoSize, todo)
  ) in
  let '(_, _, res, _) := forLoop (todoSize, todo, newArray N, inDegs) N (fun resSize p =>
    let '(todoSize, todo, res, inDegs) := p in
    let todoSize := pred todoSize in
    let n := get todo todoSize in
    let res := update res resSize n in
    let '(todoSize, todo, inDegs) := forLoop (todoSize, todo, inDegs) (get outDegs n) (fun j p =>
      let '(todoSize, todo, inDegs) := p in
      let inDegs := decrement inDegs (get (get A n) j) in
      if get inDegs (get (get A n) j) =? 0 then
        let todo := update todo todoSize (get (get A n) j) in
        let todoSize := S todoSize in
        (todoSize, todo, inDegs)
      else
        (todoSize, todo, inDegs)
    ) in
    (todoSize, todo, res, inDegs)
  ) in 
  res.
*)
End toposort.

Definition N := 6.
Definition a0 := [5].
Definition a1 := [2; 5].
Definition a2 := @nil nat.
Definition a3 := [1; 2].
Definition a4 := [1; 5].
Definition a5 := [2].
Definition A := [a0; a1; a2; a3; a4; a5].
Definition outDegs := map (@length nat) A.

Definition toposort2 := @toposort list (ListIsArray nat 0) (ListIsArray (list nat) []).

Definition result: list nat := toposort2 N A outDegs.

Goal result = [4; 3; 1; 0; 5; 2]. reflexivity. Qed.


Definition toposort3(N: nat)(A: list (list nat))(outDegs: list nat): list nat.
  set (t := toposort2 N A outDegs).
  cbv beta delta [
    toposort2 toposort increment decrement
  ] in t.
  match goal with
  | t := ?a |- _ => exact a
  end.
Defined.

Print toposort3. (* not quite what we want *)

Definition toposort4 := ltac:(let res := eval cbv beta delta [
    toposort2 toposort increment decrement
  ] in
  (fun N A outDegs => toposort2 N A outDegs) in exact res).

Print toposort4.

Definition toposort5 := ltac:(let res := eval cbv beta delta [
    toposort2 toposort increment decrement
  ] in
  (toposort2 N A outDegs) in exact res).

Print toposort5. (* this expression should hopefully be easy to reify *)

Require Import riscv.Decidable.

Inductive member{T: Type}: list T -> Type :=
  | member_here: forall h t, member (h :: t)
  | member_there: forall h t, member t -> member (h :: t).

Fixpoint member_to_index{T: Type}{l: list T}(m: member l){struct m}: nat :=
  match m with
  | member_here _ _ => 0
  | member_there _ _ m' => S (member_to_index m')
  end.

(*
Lemma member_to_index_inj: forall {T: Type} (l: list T) (x y: member l),
  member_to_index x = member_to_index y -> x = y.
Proof.
  induction l.
  - intros. inversion x.
  - intros. destruct x.
    + destruct y.
Defined.

Definition eq_dec_member{T: Type}(l: list T): DecidableEq (member l).
  intros x y. unfold Decidable.
  destruct (Nat.eq_dec (member_to_index x) (member_to_index y)).
*)

Fixpoint eq_dec_member{T: Type}(l: list T){struct l}: DecidableEq (member l).
  destruct l.
  - intros. inversion x.
  - intros.
    unfold Decidable.
    destruct x (* eqn: Ex*).
    + Fail destruct y.
Abort.

Require Import List Program.Equality.

Definition member_empty{T: Type}(m: member (@nil T)): forall (R: Type), R.
inversion m. Defined.

Definition member_discriminate: forall T (b: T) bs m, 
  member_here b bs = member_there b bs m -> False.
  intros. discriminate. Defined.

Definition invert_member_there_eq: forall T (b: T) bs x y,
  member_there b bs x = member_there b bs y -> x = y.
  intros. inversion H. apply Eqdep.EqdepTheory.inj_pair2 in H1. assumption.
Defined.

Fixpoint member_dec T (ls: list T) {struct ls}: forall (x y: member ls), {x = y} + {x <> y}.
  refine match ls with
         | nil => _
         | b :: bs => _
         end.
  - intros. apply (member_empty x).
  - dependent destruction x.
    + dependent destruction y; clear member_dec.
      * exact (left eq_refl).
      * right; intro. eapply member_discriminate. eassumption.
    + dependent destruction y.
      * right; intro. eapply member_discriminate. symmetry. eassumption.
      * destruct (member_dec _ _ x y).
        { left. f_equal. assumption. }
        { right; intro. apply n. eapply invert_member_there_eq. eassumption. }
Defined.


Eval cbv -[member_empty member_discriminate invert_member_there_eq] in member_dec.


Parameter v1 v2 v3: nat.

Definition ll := [v1; v2; v3].

Definition mm: member ll := member_there v1 _ (member_here v2 [v3]).

Definition mm': member ll := member_there v1 _ (member_there v2 _ (member_here v3 [])).

Axiom JMeq_eq_eq: forall T (x: T), JMeq_eq JMeq_refl = (@eq_refl T x).

Goal (if (member_dec _ _ mm mm') then 1 else 0) = 0.
  cbv.
  do 4 rewrite JMeq_eq_eq.
 reflexivity.
Qed.

Fixpoint member_app_r{T: Type}(l1 l2: list T)(m: member l1): member (l1 ++ l2).
  destruct l1.
  - inversion m.
  - destruct m.
    + apply member_here.
    + rewrite <- app_comm_cons. apply member_there.
      apply member_app_r. exact m.
Defined.

Fixpoint member_app_l{T: Type}(l1 l2: list T)(m: member l2): member (l1 ++ l2).
  destruct l1.
  - exact m.
  - rewrite <- app_comm_cons. apply member_there.
    apply member_app_l. exact m.
Defined.

Definition member_app_13{T: Type}(l1 l2 l3: list T)(m: member l1): member (l1 ++ l2 ++ l3).
  apply member_app_r.
  exact m.
Defined.

Definition member_app_23{T: Type}(l1 l2 l3: list T)(m: member l2): member (l1 ++ l2 ++ l3).
  apply member_app_l.
  apply member_app_r.
  exact m.
Defined.

Definition member_app_33{T: Type}(l1 l2 l3: list T)(m: member l3): member (l1 ++ l2 ++ l3).
  apply member_app_l.
  apply member_app_l.
  exact m.
Defined.

Fixpoint member_get{T: Type}{l: list T}(m: member l): T :=
  match m with
  | member_here h _ => h
  | member_there _ t m0 => member_get m0
  end.

Fixpoint member_remove{T: Type}(dec: DecidableEq T)(r: T)(l: list T)(m: member l)
  (ne: member_get m <> r) {struct m}: member (remove dec r l).
  destruct m.
  - (* here *)
    simpl in *. destruct (dec r h).
    + subst. contradiction.
    + apply member_here.
  - (* there *)
    simpl in *. destruct (dec r h).
    + subst. apply (member_remove _ _ _ _ _ ne).
    + apply member_there. apply (member_remove _ _ _ _ _ ne).
Defined.

(* Low-Level Gallina *)
Section LLG.

  Context {var: Set}.
  Context {eq_var_dec: DecidableEq var}.

  Inductive expr: list var -> nat -> Set :=
  | ELit(v: nat): expr [] 0
  | EVar(n: nat)(x: var): expr [x] n
  | ELet{n1 n2: nat}{l1 l2: list var}(x: var)(e1: expr l1 n1)(e2: expr l2 n2):
      expr (l1 ++ (remove eq_var_dec x l2)) n2
  | ENewArray(n: nat){l: list var}(size: expr l 0): expr l (S n)
  | EGet{n: nat}{l1 l2: list var}(a: expr l1 (S n))(i: expr l2 0): expr (l1 ++ l2) n
  | EUpdate{n: nat}{l1 l2 l3: list var}(a: expr l1 (S n))(i: expr l2 0)(v: expr l3 n):
      expr (l1 ++ l2 ++ l3) (S n)
   (* TODO allow several updated vars *)
  | EFor{n2 n3: nat}{l1 l2 l3: list var}(i: var)(to: expr l1 0)(updates: var)(body: expr l2 n2)
      (rest: expr l3 n3):
      expr ([updates] ++ l1 ++ (remove eq_var_dec i l2) ++ l3) n3
  .

  Definition interp_type: nat -> Type :=
    fix rec(n: nat): Type := match n with
    | O => nat
    | S m => list (rec m)
    end.

  Definition interp_type_IsArray(n: nat): IsArray (list (interp_type n)) (interp_type n) :=
    match n with
    | O => ListIsArray nat 0
    | S _ => ListIsArray _ nil
    end.

  Definition fill_in_type(x: var)(t: nat)(l: list var)(types: member (remove eq_var_dec x l) -> nat):
    (member l -> nat) :=
    fun m => match (eq_var_dec (member_get m) x) with
      | left _ => t
      | right NEq => types (member_remove eq_var_dec x l m NEq)
      end.

  Definition fill_in_val(x: var)(t: nat)(v: interp_type t)(l: list var)
    (R: member (remove eq_var_dec x l) -> nat)
    (vals: forall m : member (remove eq_var_dec x l), interp_type (R m)):
    (forall m: member l, interp_type (fill_in_type x t l R m)).
    intro m.
    unfold fill_in_type.
    destruct (eq_var_dec (member_get m) x).
    + exact v.
    + apply (vals (member_remove eq_var_dec x l m n)).
  Defined.

(*  Definition fill_in_val{tx: nat}(x: var)(v: interp_type tx)(l: list var)
    (R: member (remove eq_var_dec x l) -> V)
    (vals: forall (m: member (remove eq_var_dec x l)), R m):
    (forall (m: member l), R m). :=
    fun m => match (eq_var_dec (member_get m) x) with
      | left _ => t
      | right NEq => types (member_remove eq_var_dec x l m NEq)
      end.
*)
(*
  Definition fill_in_val{V: Type}(x: var)(v: V)(l: list var)(R: member (remove eq_var_dec x l) -> V)
    (vals: forall (m: member (remove eq_var_dec x l)), R m):
    (forall (m: member l), R m). :=
    fun m => match (eq_var_dec (member_get m) x) with
      | left _ => t
      | right NEq => types (member_remove eq_var_dec x l m NEq)
      end.
*)

  Definition update_vals(l: list var)(types: member l -> Type)(i: member l)(v: types i)
    (vals: forall m : member l, types m):
           forall m : member l, types m.
    intro m.
    (* destruct (eq_var_dec (member_get i) (member_get m)). bad because member_get not injective *)
    destruct (member_dec _ _ i m). (* <-------- TODO this does not reduce because of JMEq stuff *)
    - rewrite <- e. exact v.
    - exact (vals m).
  Defined.

  Definition TODO{T: Type}: T. Admitted.

  Fixpoint interp_expr{n: nat}{l: list var}
    (e: expr l n) (types: member l -> nat)
    {struct e}:
      option ((forall x: member l, interp_type (types x)) -> interp_type n).
    destruct e eqn: E.
    - simpl. apply Some. intro vals. exact v.
    - destruct (Nat.eq_dec n (types (member_here x []))).
      + subst n. apply Some.
        intro vals. set (v := vals (member_here x nil)).
        apply v.
      + exact None. (* error: types list doesn't match *)
    - set (o1 := interp_expr n1 l1 e0_1
        (fun (m: member l1) => types (member_app_r l1 (remove eq_var_dec x l2) m))).
      destruct o1 as [f1|].
      + set (types' := (fun m => types (member_app_l l1 (remove eq_var_dec x l2) m))).
        set (types'' := fill_in_type x n1 l2 types').
        set (o2 := interp_expr n2 l2 e0_2 types'').
        destruct o2 as [f2|].
        * apply Some. intro vals.
          specialize (f1 (fun (m: member l1) => vals  (member_app_r l1 (remove eq_var_dec x l2) m))).
          set (vals' := (fun m => vals (member_app_l l1 (remove eq_var_dec x l2) m))).
          replace (forall m : member (remove eq_var_dec x l2),
                   interp_type (types (member_app_l l1 (remove eq_var_dec x l2) m)))
             with (forall m : member (remove eq_var_dec x l2),
                   interp_type (types' m)) in vals'
             by (subst types'; reflexivity).
          subst types''.
          set (vals'' := fill_in_val x n1 f1 l2 types' vals').
          exact (f2 vals'').
        * exact None.
      + exact None.
    - set (o := interp_expr 0 l e0 types).
      simpl in o.
      destruct o as [f|].
      + apply Some. intro vals.
        specialize (f vals).
        exact (@newArray _ _ (interp_type_IsArray n) f).
      + exact None.
    - set (o1 := interp_expr _ l1 e0_1 (fun m => types (member_app_r l1 l2 m))).
      simpl in o1.
      destruct o1 as [f1|].
      + set (o2 := interp_expr _ l2 e0_2 (fun m => types (member_app_l l1 l2 m))).
        simpl in o2.
        destruct o2 as [f2|].
        * apply Some. intro vals.
          specialize (f1 (fun m => vals (member_app_r l1 l2 m))).
          specialize (f2 (fun m => vals (member_app_l l1 l2 m))).
          exact (@get _ _ (interp_type_IsArray n) f1 f2).
        * exact None.
      + exact None.
    - set (o1 := interp_expr _ l1 e0_1
        (fun m => types (member_app_13 l1 l2 l3 m))).
      simpl in o1.
      destruct o1 as [f1|].
      + set (o2 := interp_expr _ l2 e0_2 (fun m => types (member_app_23 l1 l2 l3 m))).
        simpl in o2.
        destruct o2 as [f2|].
        * set (o3 := interp_expr _ l3 e0_3 (fun m => types (member_app_33 l1 l2 l3 m))).
          destruct o3 as [f3|].
          { apply Some. intro vals.
            specialize (f1 (fun m => vals  (member_app_13 l1 l2 l3 m))).
            specialize (f2 (fun m => vals  (member_app_23 l1 l2 l3 m))).
            specialize (f3 (fun m => vals  (member_app_33 l1 l2 l3 m))).
            exact (@update _ _ (interp_type_IsArray n) f1 f2 f3). }
          { exact None. }
        * exact None.
      + exact None.
    - set (types1 := fun m => types (member_app_l [updates] _
                                    (member_app_r _ (remove eq_var_dec i l2 ++ l3) m))).
      set (o1 := interp_expr _ l1 e0_1 types1).
      simpl in o1.
      destruct o1 as [f1|].
      + set (types20 := (fun m => types
                (member_app_l [updates] _
                (member_app_l l1 _
                (member_app_r _ l3 m))))).
        set (types2 := fill_in_type i 0 l2 types20). (* subst types20. *)
        set (o2 := interp_expr n2 l2 e0_2 types2).
        destruct o2 as [f2|].
        * set (types3 := (fun m => types
            (member_app_l [updates] _
            (member_app_l l1 _
            (member_app_l (remove eq_var_dec i l2) _ m))))).
          set (o3 := interp_expr _ l3 e0_3 types3).
          destruct o3 as [f3|].
          { apply Some. intro vals.
            set (vals1 := (fun m => vals (member_app_l [updates] _
                                         (member_app_r _ (remove eq_var_dec i l2 ++ l3) m)))).
            let t := type of vals1 in
            replace t
               with (forall m : member l1, interp_type (types1 m)) in vals1
               by (subst types1; reflexivity).
            specialize (f1 vals1).
            rename i into var_i, updates into var_updates.
            set (updates := vals (member_here _ _)).
            (* note: refine will "intro" the "let" created by the for loop *)
            simple refine (for i from 0 to f1 updating (updates) {{
                       _
            }} ;; _).
            { set (vals' := update_vals _ (fun m => interp_type (types m)) _ updates vals).
              set (vals20 := (fun m => vals'
                    (member_app_l [var_updates] _
                    (member_app_l l1 _
                    (member_app_r _ l3 m))))).
              let t := type of vals20 in
              replace t
                 with (forall m : member (remove eq_var_dec var_i l2),
                       interp_type (types20 m)) in vals20
              by (subst types20; reflexivity).
              set (vals2 := fill_in_val var_i 0 f1 l2 types20 vals20).
              let t := type of vals2 in
              replace t with (forall m : member l2, interp_type (types2 m)) in vals2
              by (subst types2; reflexivity).
              specialize (f2 vals2).
              Fail (exact f2). apply TODO. }
            { apply TODO. }
          }
          { exact None. }
        * exact None.
      + exact None.
  Defined.

  (*
  Definition interp_expr{n: nat}{l: list var}:
    forall (e: expr l n) (types: member l -> nat) (vals: forall x: member l, interp_type (types x)),
      option (interp_type n) :=
  fix rec(e: expr l n) (types: member l -> nat) (vals: forall x: member l, interp_type (types x)) :=
    match e with
    | EVar x => None
    | ELet x e1 e2 => None 
    | ENewArray size init => None
    | EGet a i => None
    | EUpdate a i v => None
    | EFor i to updates body rest => None
    end.

  Inductive expr: forall (fvs: list var) (types: member fvs -> nat) (retType: nat), Set :=
  (* how to join two possibly contradictory types envs eg in ELet ? *)
  *)

  (*
  Inductive expr: nat -> Set :=
  | EVar{n: nat}(x: var): expr n
  | ELet{n1 n2: nat}(x: var)(e1: expr n1)(e2: expr n2): expr n2
  | ENewArray{n: nat}(size: expr 0)(init: expr n): expr (S n)
  | EGet{n: nat}(a: expr (S n))(i: expr 0): expr n
  | EUpdate{n: nat}(a: expr (S n))(i: expr 0)(v: expr n): expr (S n)
  | EFor{n: nat}(i: var)(to: expr 0)(updates: var (* TODO allow several *))(body: expr n): expr n
  .

  Definition interp_expr{n: nat}: expr n -> option (interp_type n) :=
    fix rec(e: expr n) := match e with
    | EVar x => None
    | ELet x e1 e2 => None 
    | ENewArray size init => None
    | EGet a i => None
    | EUpdate a i v => None
    | EFor i to updates body => None
    end.
     how to deal with binders? Actually, if e has a free variable of type T, 
     the return type of interp_expr should be "option (T -> ...)" instead *)

End LLG.

Definition test1(v1 v2: nat): nat := let x1 := v1 in let x2 := v2 in x1.

Definition myvar := nat.
Definition var_x1: myvar := 1.
Definition var_x2: myvar := 2.

Definition test1a(v1 v2: nat): expr (@nil myvar) 0 :=
  ELet var_x1 (ELit v1) (ELet var_x2 (ELit v2) (EVar 0 var_x1)).

Definition empty_types: member (@nil myvar) -> nat. intro. inversion H. Defined.
Definition empty_vals: forall m : member (@nil myvar), interp_type (empty_types m).
  intro. inversion m. Defined.

Definition interp_expr'{n: nat}(e: expr (@nil myvar) n): option (interp_type n) :=
  match interp_expr e empty_types with
  | Some f => Some (f empty_vals)
  | None => None
  end.

Goal forall v1 v2, Some (test1 v1 v2) = interp_expr' (test1a v1 v2).
  intros. reflexivity.
Qed.

Definition ListWithDefault0IsArray := ListIsArray nat 0.
Existing Instance ListWithDefault0IsArray.

Definition test2(i v: nat): nat :=
  let x1 := newArray 3 in
  let x2 := update x1 i v in
  get x2 i.

Definition test2a(i v: nat): expr (@nil myvar) 0 :=
  ELet var_x1 (ENewArray 0 (ELit 3))
  (ELet var_x2 (EUpdate (EVar 1 var_x1) (ELit i) (ELit v))
  (EGet (EVar 1 var_x2) (ELit i))).

Goal forall i v, Some (test2 i v) = interp_expr' (test2a i v).
  intros. unfold interp_expr', interp_expr. reflexivity.
Qed.
