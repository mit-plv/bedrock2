Require Import PyLevelLang.Language.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString.

Local Open Scope Z_scope.

Fixpoint interp_type (t : type) :=
  match t with
  | TInt => Z
  | TBool => bool
  | TString => string
  | TPair _ t1 t2 => prod (interp_type t1) (interp_type t2)
  | TList t' => list (interp_type t')
  | TEmpty => unit
  end.

Fixpoint default_val (t : type) : interp_type t :=
  match t as t' return interp_type t' with
  | TInt => 0
  | TBool => false
  | TString => EmptyString
  | TPair _ t1 t2 => (default_val t1, default_val t2)
  | TList t' => nil
  | TEmpty => tt
  end.

Fixpoint eval_range (lo : Z) (len : nat) : list Z :=
  match len with
  | 0%nat => nil
  | S n => lo :: eval_range (lo + 1) n
  end.

Definition proj_expected (t_expected : type) (v : {t_actual & interp_type t_actual}) : 
  interp_type t_expected :=
  match type_eq_dec (projT1 v) t_expected with
  | left H => cast H _ (projT2 v)
  | _ => default_val t_expected
  end.

Definition eqb_values {t : type} (H : can_eq t = true) :
  interp_type t -> interp_type t -> bool.
Proof.
  refine (
  match t as t' return can_eq t' = true -> interp_type t' -> interp_type t' -> bool with
  | TInt => fun _ => Z.eqb
  | TString => fun _ => String.eqb
  | TBool => fun _ => Bool.eqb
  | TEmpty => fun _ => fun _ _ => true
  | _ => _
  end H); easy.
Defined.

Section WithMap.
  Context {locals: map.map string {t & interp_type t}} {locals_ok: map.ok locals}.

  Definition get_local (l : locals) {t : type} (x : string) : interp_type t :=
    match map.get l x with
    | Some v => proj_expected _ v
    | None => default_val _
    end.

  Definition set_local (l : locals) {t : type} (x : string) (v : interp_type t) :
    locals := map.put l x (existT _ _ v).

  Definition interp_atom {t : type} (a : atom t) : interp_type t :=
    match a with
    | AInt n => n
    | ABool b => b
    | AString s => s
    | ANil t => nil
    | AEmpty => tt
    end.

  Definition interp_unop {t1 t2 : type} (o : unop t1 t2) :
    interp_type t1 -> interp_type t2 :=
    match o in unop t1 t2 return interp_type t1 -> interp_type t2 with
    | ONeg => Z.sub 0
    | ONot => negb
    | OLength _ => fun x => Z.of_nat (length x)
    | OLengthString => fun x => Z.of_nat (String.length x)
    | OFst _ _ _ => fst
    | OSnd _ _ _ => snd
    end.

  Definition interp_binop {t1 t2 t3: type} (o : binop t1 t2 t3) : 
    interp_type t1 -> interp_type t2 -> interp_type t3 := 
    match o in binop t1 t2 t3 
    return interp_type t1 -> interp_type t2 -> interp_type t3 with 
    | OPlus =>  Z.add
    | OMinus => Z.sub
    | OTimes => Z.mul
    | ODiv => Z.div
    | OMod => Z.modulo
    | OAnd => andb
    | OOr => orb
    | OConcat _ => fun a b => app a b
    | OConcatString => String.append
    | OLess => Z.ltb
    | OEq _ H => eqb_values H
    | ORepeat _ => fun l n => concat (repeat l (Z.to_nat n))
    | OPair _ _ _ => pair
    | OCons _ => cons
    | ORange => fun s e => eval_range s (Z.to_nat (e - s))
    end.

  Fixpoint interp_expr (l : locals) {t : type} (e : expr t) : interp_type t :=
    match e in (expr t0) return (interp_type t0) with
    | EVar _ x | ELoc _ x => get_local l x
    | EAtom a => interp_atom a
    | EUnop o e1 => interp_unop o (interp_expr l e1)
    | EBinop o e1 e2 => interp_binop o (interp_expr l e1) (interp_expr l e2)
    | EFlatmap l1 x fn => flat_map (fun y => interp_expr (set_local l x y) fn) (interp_expr l l1)
    | EIf e1 e2 e3 => if interp_expr l e1 then interp_expr l e2 else interp_expr l e3
    | EFold l1 a x y fn => let l1' := interp_expr l l1 in
                             let a' := interp_expr l a in
                             let fn' := fun v acc => interp_expr (set_local (set_local l x v) y acc) fn in
                             fold_right fn' a' l1'
    | ELet x e1 e2 => interp_expr (set_local l x (interp_expr l e1)) e2
    end.

  Fixpoint interp_command (l : locals) (c : command) : locals :=
    match c with
    | CSkip => l
    | CSeq c1 c2 => interp_command (interp_command l c1) c2
    | CLet x e c1 | CLetMut x e c1 => let l' := interp_command (set_local l x (interp_expr l e)) c1 in
                                      map.update l' x (map.get l x)
    | CGets x e => set_local l x (interp_expr l e)
    | CIf e c1 c2 => if interp_expr l e then interp_command l c1 else interp_command l c2
    | CForeach x e c1 => let l' := fold_left (fun l' v => interp_command (set_local l' x v) c1) (interp_expr l e) l in
                         map.update l' x (map.get l x)
    end.
End WithMap.
