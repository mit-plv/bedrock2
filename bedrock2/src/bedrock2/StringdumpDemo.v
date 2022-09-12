Require Import Coq.Strings.String.

Definition TAB: String.string := String.String (Ascii.ascii_of_nat  9) String.EmptyString.
Definition LF : String.string := String.String (Ascii.ascii_of_nat 10) String.EmptyString.

Local Open Scope string_scope.

Definition mytext := LF ++
LF ++
"hello world {" ++ LF ++
TAB ++ "// indented text above empty line" ++ LF ++
LF ++
"    space-indented" ++ LF ++
"}" ++ LF ++
String.concat ", " (List.repeat "a long line" 20) ++ LF ++
"i" ++ TAB ++ "i^2" ++ LF ++
"4" ++ TAB ++ "16" ++ LF ++
"10" ++ TAB ++ "100" ++ LF ++
LF.

(* Doesn't work because it also prints an equal sign, quotes, and the types, *)
(* instead of just the string: *)
(* Compute mytext. *)

Require Import bedrock2.Stringdump.
Local Open Scope stringdump_scope.
Close Scope string_scope.
Undelimit Scope string_scope.

Goal True.
  (* Creates file "StringdumpDemo.out" in the current working directory: *)
  Redirect "StringdumpDemo" let r := eval vm_compute in mytext in idtac r.
  (* Note that this behaves differently in ProofGeneral vs when compiled using make:
     - In ProofGeneral, the current working directory is set to the directory of
       this file, and the output is surrounded by <infomsg>...</infomsg>.
     - When compiled using make, the current working directory is the directory
       containing the Makefile, and there's no <infomsg>...</infomsg> around the output.
     So it is recommended to only use the .out files created by make, and to ignore those
     created during interactive editing.
     Also note that the file contains an extra newline at the end. *)
Abort.
