Require Import Coq.Strings.String Coq.Strings.HexString. 
Require Import Coq.Init.Byte coqutil.Byte.
Require Import Coq.Lists.List.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Local Open Scope string_scope.
Local Open Scope list_scope.
Import ListNotations.
Local Coercion String.list_byte_of_string : string >-> list.

(* USAGE:
Definition mysymbols := Symbols.symbols myfinfo.
./etc/bytedump.sh MyRepo.MyFile.mysymbols > /tmp/l.s
riscv64-elf-gcc -T mylinkerscript.lds -g -nostdlib /tmp/l.s -o /tmp/l
*)

Definition symbols {map : map.map string BinNums.Z} (finfo : map) : list byte := 
  ".globl _start" ++ [x0a] ++
  "_start:" ++ [x0a] ++
  List.flat_map (A:=_*string) (fun '(a, s) =>
    ".org " ++ HexString.of_Z a ++ [x0a] ++
    ".local " ++ s ++ [x0a] ++
    s ++ ":" ++ [x0a])
  (SortedList.value (map.fold (fun m k v => map.put m v k) map.empty finfo)).
