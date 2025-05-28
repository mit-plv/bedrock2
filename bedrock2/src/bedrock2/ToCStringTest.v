Require Import bedrock2.Syntax bedrock2.NotationsCustomEntry.

Import Syntax.Coercions BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition main := func! () ~> (r) {
  r = $0;
  v = $(expr.inlinetable access_size.one [Byte.x00; Byte.x01] 1);
  require v;

  require $(expr.inlinetable access_size.one [Byte.x00; Byte.x01] 1);

  stackalloc 1 as p;
  store1(p, $1);
  require load1(p);

  require (p+$1 == $1 + p);
  require (p*$1 == $1 * p);
  require (p<<$31 == (p&$1) * $(2^31));

  r = $1
}.

From coqutil.Macros Require Import WithBaseName.
From bedrock2 Require Import ToCString.

Definition test := String.list_byte_of_string (c_module &[,main]).
