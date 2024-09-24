From Coq Require Import String HexString.
From Coq.Init Require Import Byte.
Require Import coqutil.Byte.
From Coq Require Import List.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Local Open Scope string_scope.
Local Open Scope list_scope.
Import ListNotations.

(* USAGE:
Definition mysymbols := Symbols.symbols myfinfo.
./etc/bytedump.py MyRepo.MyFile.mysymbols > /tmp/l.s
riscv64-elf-gcc -T mylinkerscript.lds -g -nostdlib /tmp/l.s -o /tmp/l
*)

Definition LF : string := String (Coq.Strings.Ascii.Ascii false true false true false false false false) "".

Definition symbols_string (finfo : list (string * BinInt.Z)) : string :=
  ".globl _start" ++ LF ++
  "_start:" ++ LF ++
  String.concat "" (List.map (fun '(a, s) =>
    ".org " ++ HexString.of_Z a ++ LF ++
    ".local " ++ s ++ LF ++
    s ++ ":" ++ LF)%string
    (SortedList.value (List.fold_right (fun '(k, v) m => map.put m v k) map.empty finfo))).

Definition symbols (finfo : list (string * BinInt.Z)) : list byte :=
  String.list_byte_of_string (symbols_string finfo).
