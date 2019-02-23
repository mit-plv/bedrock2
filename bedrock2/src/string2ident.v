From coqutil Require Import subst.
Require Import Coq.Strings.String.
Open Scope string_scope.

Definition with_name (n : string) {T} (v : T) := v.

(* WHY and in which cases is one fresh not enough, Jason? *)
Ltac multifresh H :=
  multimatch constr:(Set) with
  | _ => let H := fresh H in H
  | _ => let H := fresh H in multifresh H
  end.
Ltac rename_to_different H := once (idtac;
  let G := fresh H in
  rename H into G;
  assert_succeeds (set (H := Set))).
Ltac ensure_free H :=
  match constr:(Set) with
  | _ => assert_succeeds (set (H := Set))
  | _ => rename_to_different H
  end.

Ltac requrieAsciiLiteral c := idtac. (* TODO *)
Ltac requireStringLiteral s := idtac. (* TODO *)

Module Context.
  Inductive list :=
  | nil
  | cons (name : string) (name_ident : Set -> Set) (rest : list).
End Context.

Ltac learn e :=
  match e with
  | let n := ?s in ?C =>
    let __ := match constr:(Set) with _ => requireStringLiteral s end in
    let lctxC := constr:(let nn := s in ltac:(
                                          let C := constr:(subst! nn for n in C) in
                                          let ctxC := learn C in exact ctxC)) in
    let ctxC := lazymatch lctxC with let _ := _ in ?ctxC => ctxC end in
    constr:(Context.cons s (fun n => n) ctxC)
  | _ => Context.nil
  end.

Ltac lookup s ctx :=
  lazymatch ctx with
  | context[Context.cons s (fun n => _) _] => n
  end.

Goal let x := "x" in let y := "y" in forall (a : with_name "x" nat) (b : with_name "y" nat), a + b = b + a.
Proof.
  let G := lazymatch goal with |- ?G => G end in
  let ctx := learn G in
  pose ctx as STRING_TO_IDENT.

  let ctx := STRING_TO_IDENT in
  let ctx := eval cbv [ctx] in ctx in
  let s := constr:("x") in
  let n := lookup s ctx in
  ensure_free n;
  intro n.
Abort.
