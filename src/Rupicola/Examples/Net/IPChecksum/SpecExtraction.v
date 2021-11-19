Require Import Rupicola.Examples.Net.IPChecksum.IPChecksum.

Require Import ZArith ExtrOcamlZInt ExtrOcamlNatInt ExtrOcamlNativeString.
Extract Inlined Constant Byte.to_N => "Char.code".
Extract Inlined Constant Z.land => "(land)".
Extract Inlined Constant Z.lor => "(lor)".
Extract Inlined Constant Z.lxor => "(lxor)".
Extract Inlined Constant Z.shiftl => "Int.shift_left".
Extract Inlined Constant Z.shiftr => "Int.shift_right".
Goal forall COQTOP_CRAP_ENDS_HERE : Set, COQTOP_CRAP_ENDS_HERE.
  Recursive Extraction Spec.ip_checksum.
  idtac "let list_char_of_string s = List.init (String.length s) (String.get s)
let () =
  Callback.register ""ip_checksum"" ip_checksum;
  Callback.register ""list_char_of_string"" list_char_of_string".
Abort.
