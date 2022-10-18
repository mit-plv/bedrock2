Require Import Ltac2.Ltac2 Ltac2.Printf Coq.Strings.Ascii.
(* Usage: see etc/bytedump.py and its invocation in bedrock2/Makefile *)

Module Unsafe.
  (* 0.6s/10k *)
  Ltac2 char_of_constr_byte (b : constr) :=
    let t := constr:(true) in
    match Constr.Unsafe.kind (eval cbv in (ascii_of_byte $b)) with
    | Constr.Unsafe.App _ args => Char.of_int
      (Int.add (match Constr.equal (Array.get args 0) t with true => 1 | false => 0 end) (Int.mul 2 (
      (Int.add (match Constr.equal (Array.get args 1) t with true => 1 | false => 0 end) (Int.mul 2 (
      (Int.add (match Constr.equal (Array.get args 2) t with true => 1 | false => 0 end) (Int.mul 2 (
      (Int.add (match Constr.equal (Array.get args 3) t with true => 1 | false => 0 end) (Int.mul 2 (
      (Int.add (match Constr.equal (Array.get args 4) t with true => 1 | false => 0 end) (Int.mul 2 (
      (Int.add (match Constr.equal (Array.get args 5) t with true => 1 | false => 0 end) (Int.mul 2 (
      (Int.add (match Constr.equal (Array.get args 6) t with true => 1 | false => 0 end) (Int.mul 2 (
      (Int.add (match Constr.equal (Array.get args 7) t with true => 1 | false => 0 end) 0))))))))))))))))))))))
    | _ => Control.throw No_value
    end.
  
  (* 1.2s/10k:
  Ltac2 char_of_constr_byte (b : constr) :=
    match Constr.Unsafe.kind constr:(Byte.byte) with
    | Constr.Unsafe.Ind byte byteinstance =>
      let rec f i :=
        match Constr.equal b (Constr.Unsafe.make (Constr.Unsafe.Constructor (Constr.Unsafe.constructor byte i) byteinstance)) with
        | true => i
        | _ => f (Int.add 1 i)
        end in Char.of_int (f 0)
    | _ => Char.of_int 0
    end .
  *)
  
  Ltac2 rec length_constr_list (xs : constr) : int :=
    match Constr.Unsafe.kind xs with
    | Constr.Unsafe.App _ args =>
      match Int.equal (Array.length args) 3 with
      | true => Int.add 1 (length_constr_list (Array.get args 2))
      | _ => 0
      end
    | Constr.Unsafe.Constructor _ _ => 0
    | _ => Control.throw No_value
    end.
  
  Ltac2 string_of_constr_list_byte (bs : constr) :=
    let buf := String.make (length_constr_list bs) (Char.of_int 0) in
    let rec fill (i : int)(bs : constr) :=
      match Constr.Unsafe.kind bs with
      | Constr.Unsafe.App _ args =>
        match Int.equal (Array.length args) 3 with
        | true =>
            String.set buf i (char_of_constr_byte (Array.get args 1));
            fill  (Int.add i 1) (Array.get args 2)
        | false => ()
        end
      | _ => Control.throw No_value
      end in
    fill 0 bs; buf.
End Unsafe.

Ltac2 string_of_constr_list_byte (bs : constr) :=
  let bs := eval vm_compute in ($bs : list Byte.byte) in
  Unsafe.string_of_constr_list_byte bs.

Ltac2 print_list_byte (bs : constr) := printf "%s" (string_of_constr_list_byte bs).
Ltac print_list_byte := ltac2:(bs |- print_list_byte (Option.get (Ltac1.to_constr bs))).

Ltac2 Notation "print_bytes" bs(constr) := print_list_byte bs.
Tactic Notation "print_bytes" constr(bs) := print_list_byte bs.


Require Import Coq.Lists.List.
Definition allBytes: list Byte.byte :=
  map (fun nn => match Byte.of_N (BinNat.N.of_nat nn) with
                 | Some b => b
                 | None => Byte.x00 (* won't happen *)
                 end)
      (seq 0 256).

(*
Import ListNotations.
Goal True.
  Time print_bytes ([Byte.x41] ++ List.repeat Byte.x20 10000 ++ [Byte.x41]).
Abort.
*)
