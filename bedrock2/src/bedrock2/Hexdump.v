(* Don't "Require Import", because otherwise string notations for bytes will be activated *)
Require Coq.Init.Byte.

(* Usage:
Require Import bedrock2.Hexdump.
Local Open Scope hexdump_scope.
Goal False.
  let bytes := eval cbv in ... in
  idtac bytes.
Abort.
*)

(* Files that require Hexdump.v should not be required by other files
   because Hexdump configures 2-digit hex strings such as 'af' as
   keywords. *)

Declare Scope hexdump_scope.
Delimit Scope hexdump_scope with hexdump.

Notation "" := (@nil Byte.byte) (only printing, right associativity, at level 3) : hexdump_scope.
Notation "a b" :=
  (@cons Byte.byte a%hexdump b%hexdump)
  (only printing, right associativity, at level 3, format "a b")
  : hexdump_scope.
Notation "a b c d xs" :=
  (@cons Byte.byte a%hexdump (b%hexdump::c%hexdump::d%hexdump::xs%hexdump))%list
  (only printing, right associativity, at level 3, format "a  b  c  d   xs")
  : hexdump_scope.
Notation "x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 xs" :=
  (@cons Byte.byte x1%hexdump (x2%hexdump::x3%hexdump::x4%hexdump::x5%hexdump::x6%hexdump::x7%hexdump::x8%hexdump::x9%hexdump::x10%hexdump::x11%hexdump::x12%hexdump::x13%hexdump::x14%hexdump::x15%hexdump::x16%hexdump::x17%hexdump::x18%hexdump::x19%hexdump::x20%hexdump::x21%hexdump::x22%hexdump::x23%hexdump::x24%hexdump::x25%hexdump::x26%hexdump::x27%hexdump::x28%hexdump::x29%hexdump::x30%hexdump::x31%hexdump::x32%hexdump::xs%hexdump))%list
  (only printing, right associativity, at level 3, format "x1  x2  x3  x4   x5  x6  x7  x8   x9  x10  x11  x12   x13  x14  x15  x16   x17  x18  x19  x20   x21  x22  x23  x24   x25  x26  x27  x28   x29  x30  x31  x32 '//' xs")
  : hexdump_scope.

Undelimit Scope hexdump_scope.

Notation "'00'" := (Byte.x00) (only printing) : hexdump_scope.
Notation "'01'" := (Byte.x01) (only printing) : hexdump_scope.
Notation "'02'" := (Byte.x02) (only printing) : hexdump_scope.
Notation "'03'" := (Byte.x03) (only printing) : hexdump_scope.
Notation "'04'" := (Byte.x04) (only printing) : hexdump_scope.
Notation "'05'" := (Byte.x05) (only printing) : hexdump_scope.
Notation "'06'" := (Byte.x06) (only printing) : hexdump_scope.
Notation "'07'" := (Byte.x07) (only printing) : hexdump_scope.
Notation "'08'" := (Byte.x08) (only printing) : hexdump_scope.
Notation "'09'" := (Byte.x09) (only printing) : hexdump_scope.
Notation "'0a'" := (Byte.x0a) (only printing) : hexdump_scope.
Notation "'0b'" := (Byte.x0b) (only printing) : hexdump_scope.
Notation "'0c'" := (Byte.x0c) (only printing) : hexdump_scope.
Notation "'0d'" := (Byte.x0d) (only printing) : hexdump_scope.
Notation "'0e'" := (Byte.x0e) (only printing) : hexdump_scope.
Notation "'0f'" := (Byte.x0f) (only printing) : hexdump_scope.
Notation "'10'" := (Byte.x10) (only printing) : hexdump_scope.
Notation "'11'" := (Byte.x11) (only printing) : hexdump_scope.
Notation "'12'" := (Byte.x12) (only printing) : hexdump_scope.
Notation "'13'" := (Byte.x13) (only printing) : hexdump_scope.
Notation "'14'" := (Byte.x14) (only printing) : hexdump_scope.
Notation "'15'" := (Byte.x15) (only printing) : hexdump_scope.
Notation "'16'" := (Byte.x16) (only printing) : hexdump_scope.
Notation "'17'" := (Byte.x17) (only printing) : hexdump_scope.
Notation "'18'" := (Byte.x18) (only printing) : hexdump_scope.
Notation "'19'" := (Byte.x19) (only printing) : hexdump_scope.
Notation "'1a'" := (Byte.x1a) (only printing) : hexdump_scope.
Notation "'1b'" := (Byte.x1b) (only printing) : hexdump_scope.
Notation "'1c'" := (Byte.x1c) (only printing) : hexdump_scope.
Notation "'1d'" := (Byte.x1d) (only printing) : hexdump_scope.
Notation "'1e'" := (Byte.x1e) (only printing) : hexdump_scope.
Notation "'1f'" := (Byte.x1f) (only printing) : hexdump_scope.
Notation "'20'" := (Byte.x20) (only printing) : hexdump_scope.
Notation "'21'" := (Byte.x21) (only printing) : hexdump_scope.
Notation "'22'" := (Byte.x22) (only printing) : hexdump_scope.
Notation "'23'" := (Byte.x23) (only printing) : hexdump_scope.
Notation "'24'" := (Byte.x24) (only printing) : hexdump_scope.
Notation "'25'" := (Byte.x25) (only printing) : hexdump_scope.
Notation "'26'" := (Byte.x26) (only printing) : hexdump_scope.
Notation "'27'" := (Byte.x27) (only printing) : hexdump_scope.
Notation "'28'" := (Byte.x28) (only printing) : hexdump_scope.
Notation "'29'" := (Byte.x29) (only printing) : hexdump_scope.
Notation "'2a'" := (Byte.x2a) (only printing) : hexdump_scope.
Notation "'2b'" := (Byte.x2b) (only printing) : hexdump_scope.
Notation "'2c'" := (Byte.x2c) (only printing) : hexdump_scope.
Notation "'2d'" := (Byte.x2d) (only printing) : hexdump_scope.
Notation "'2e'" := (Byte.x2e) (only printing) : hexdump_scope.
Notation "'2f'" := (Byte.x2f) (only printing) : hexdump_scope.
Notation "'30'" := (Byte.x30) (only printing) : hexdump_scope.
Notation "'31'" := (Byte.x31) (only printing) : hexdump_scope.
Notation "'32'" := (Byte.x32) (only printing) : hexdump_scope.
Notation "'33'" := (Byte.x33) (only printing) : hexdump_scope.
Notation "'34'" := (Byte.x34) (only printing) : hexdump_scope.
Notation "'35'" := (Byte.x35) (only printing) : hexdump_scope.
Notation "'36'" := (Byte.x36) (only printing) : hexdump_scope.
Notation "'37'" := (Byte.x37) (only printing) : hexdump_scope.
Notation "'38'" := (Byte.x38) (only printing) : hexdump_scope.
Notation "'39'" := (Byte.x39) (only printing) : hexdump_scope.
Notation "'3a'" := (Byte.x3a) (only printing) : hexdump_scope.
Notation "'3b'" := (Byte.x3b) (only printing) : hexdump_scope.
Notation "'3c'" := (Byte.x3c) (only printing) : hexdump_scope.
Notation "'3d'" := (Byte.x3d) (only printing) : hexdump_scope.
Notation "'3e'" := (Byte.x3e) (only printing) : hexdump_scope.
Notation "'3f'" := (Byte.x3f) (only printing) : hexdump_scope.
Notation "'40'" := (Byte.x40) (only printing) : hexdump_scope.
Notation "'41'" := (Byte.x41) (only printing) : hexdump_scope.
Notation "'42'" := (Byte.x42) (only printing) : hexdump_scope.
Notation "'43'" := (Byte.x43) (only printing) : hexdump_scope.
Notation "'44'" := (Byte.x44) (only printing) : hexdump_scope.
Notation "'45'" := (Byte.x45) (only printing) : hexdump_scope.
Notation "'46'" := (Byte.x46) (only printing) : hexdump_scope.
Notation "'47'" := (Byte.x47) (only printing) : hexdump_scope.
Notation "'48'" := (Byte.x48) (only printing) : hexdump_scope.
Notation "'49'" := (Byte.x49) (only printing) : hexdump_scope.
Notation "'4a'" := (Byte.x4a) (only printing) : hexdump_scope.
Notation "'4b'" := (Byte.x4b) (only printing) : hexdump_scope.
Notation "'4c'" := (Byte.x4c) (only printing) : hexdump_scope.
Notation "'4d'" := (Byte.x4d) (only printing) : hexdump_scope.
Notation "'4e'" := (Byte.x4e) (only printing) : hexdump_scope.
Notation "'4f'" := (Byte.x4f) (only printing) : hexdump_scope.
Notation "'50'" := (Byte.x50) (only printing) : hexdump_scope.
Notation "'51'" := (Byte.x51) (only printing) : hexdump_scope.
Notation "'52'" := (Byte.x52) (only printing) : hexdump_scope.
Notation "'53'" := (Byte.x53) (only printing) : hexdump_scope.
Notation "'54'" := (Byte.x54) (only printing) : hexdump_scope.
Notation "'55'" := (Byte.x55) (only printing) : hexdump_scope.
Notation "'56'" := (Byte.x56) (only printing) : hexdump_scope.
Notation "'57'" := (Byte.x57) (only printing) : hexdump_scope.
Notation "'58'" := (Byte.x58) (only printing) : hexdump_scope.
Notation "'59'" := (Byte.x59) (only printing) : hexdump_scope.
Notation "'5a'" := (Byte.x5a) (only printing) : hexdump_scope.
Notation "'5b'" := (Byte.x5b) (only printing) : hexdump_scope.
Notation "'5c'" := (Byte.x5c) (only printing) : hexdump_scope.
Notation "'5d'" := (Byte.x5d) (only printing) : hexdump_scope.
Notation "'5e'" := (Byte.x5e) (only printing) : hexdump_scope.
Notation "'5f'" := (Byte.x5f) (only printing) : hexdump_scope.
Notation "'60'" := (Byte.x60) (only printing) : hexdump_scope.
Notation "'61'" := (Byte.x61) (only printing) : hexdump_scope.
Notation "'62'" := (Byte.x62) (only printing) : hexdump_scope.
Notation "'63'" := (Byte.x63) (only printing) : hexdump_scope.
Notation "'64'" := (Byte.x64) (only printing) : hexdump_scope.
Notation "'65'" := (Byte.x65) (only printing) : hexdump_scope.
Notation "'66'" := (Byte.x66) (only printing) : hexdump_scope.
Notation "'67'" := (Byte.x67) (only printing) : hexdump_scope.
Notation "'68'" := (Byte.x68) (only printing) : hexdump_scope.
Notation "'69'" := (Byte.x69) (only printing) : hexdump_scope.
Notation "'6a'" := (Byte.x6a) (only printing) : hexdump_scope.
Notation "'6b'" := (Byte.x6b) (only printing) : hexdump_scope.
Notation "'6c'" := (Byte.x6c) (only printing) : hexdump_scope.
Notation "'6d'" := (Byte.x6d) (only printing) : hexdump_scope.
Notation "'6e'" := (Byte.x6e) (only printing) : hexdump_scope.
Notation "'6f'" := (Byte.x6f) (only printing) : hexdump_scope.
Notation "'70'" := (Byte.x70) (only printing) : hexdump_scope.
Notation "'71'" := (Byte.x71) (only printing) : hexdump_scope.
Notation "'72'" := (Byte.x72) (only printing) : hexdump_scope.
Notation "'73'" := (Byte.x73) (only printing) : hexdump_scope.
Notation "'74'" := (Byte.x74) (only printing) : hexdump_scope.
Notation "'75'" := (Byte.x75) (only printing) : hexdump_scope.
Notation "'76'" := (Byte.x76) (only printing) : hexdump_scope.
Notation "'77'" := (Byte.x77) (only printing) : hexdump_scope.
Notation "'78'" := (Byte.x78) (only printing) : hexdump_scope.
Notation "'79'" := (Byte.x79) (only printing) : hexdump_scope.
Notation "'7a'" := (Byte.x7a) (only printing) : hexdump_scope.
Notation "'7b'" := (Byte.x7b) (only printing) : hexdump_scope.
Notation "'7c'" := (Byte.x7c) (only printing) : hexdump_scope.
Notation "'7d'" := (Byte.x7d) (only printing) : hexdump_scope.
Notation "'7e'" := (Byte.x7e) (only printing) : hexdump_scope.
Notation "'7f'" := (Byte.x7f) (only printing) : hexdump_scope.
Notation "'80'" := (Byte.x80) (only printing) : hexdump_scope.
Notation "'81'" := (Byte.x81) (only printing) : hexdump_scope.
Notation "'82'" := (Byte.x82) (only printing) : hexdump_scope.
Notation "'83'" := (Byte.x83) (only printing) : hexdump_scope.
Notation "'84'" := (Byte.x84) (only printing) : hexdump_scope.
Notation "'85'" := (Byte.x85) (only printing) : hexdump_scope.
Notation "'86'" := (Byte.x86) (only printing) : hexdump_scope.
Notation "'87'" := (Byte.x87) (only printing) : hexdump_scope.
Notation "'88'" := (Byte.x88) (only printing) : hexdump_scope.
Notation "'89'" := (Byte.x89) (only printing) : hexdump_scope.
Notation "'8a'" := (Byte.x8a) (only printing) : hexdump_scope.
Notation "'8b'" := (Byte.x8b) (only printing) : hexdump_scope.
Notation "'8c'" := (Byte.x8c) (only printing) : hexdump_scope.
Notation "'8d'" := (Byte.x8d) (only printing) : hexdump_scope.
Notation "'8e'" := (Byte.x8e) (only printing) : hexdump_scope.
Notation "'8f'" := (Byte.x8f) (only printing) : hexdump_scope.
Notation "'90'" := (Byte.x90) (only printing) : hexdump_scope.
Notation "'91'" := (Byte.x91) (only printing) : hexdump_scope.
Notation "'92'" := (Byte.x92) (only printing) : hexdump_scope.
Notation "'93'" := (Byte.x93) (only printing) : hexdump_scope.
Notation "'94'" := (Byte.x94) (only printing) : hexdump_scope.
Notation "'95'" := (Byte.x95) (only printing) : hexdump_scope.
Notation "'96'" := (Byte.x96) (only printing) : hexdump_scope.
Notation "'97'" := (Byte.x97) (only printing) : hexdump_scope.
Notation "'98'" := (Byte.x98) (only printing) : hexdump_scope.
Notation "'99'" := (Byte.x99) (only printing) : hexdump_scope.
Notation "'9a'" := (Byte.x9a) (only printing) : hexdump_scope.
Notation "'9b'" := (Byte.x9b) (only printing) : hexdump_scope.
Notation "'9c'" := (Byte.x9c) (only printing) : hexdump_scope.
Notation "'9d'" := (Byte.x9d) (only printing) : hexdump_scope.
Notation "'9e'" := (Byte.x9e) (only printing) : hexdump_scope.
Notation "'9f'" := (Byte.x9f) (only printing) : hexdump_scope.
Notation "'a0'" := (Byte.xa0) (only printing) : hexdump_scope.
Notation "'a1'" := (Byte.xa1) (only printing) : hexdump_scope.
Notation "'a2'" := (Byte.xa2) (only printing) : hexdump_scope.
Notation "'a3'" := (Byte.xa3) (only printing) : hexdump_scope.
Notation "'a4'" := (Byte.xa4) (only printing) : hexdump_scope.
Notation "'a5'" := (Byte.xa5) (only printing) : hexdump_scope.
Notation "'a6'" := (Byte.xa6) (only printing) : hexdump_scope.
Notation "'a7'" := (Byte.xa7) (only printing) : hexdump_scope.
Notation "'a8'" := (Byte.xa8) (only printing) : hexdump_scope.
Notation "'a9'" := (Byte.xa9) (only printing) : hexdump_scope.
Notation "'aa'" := (Byte.xaa) (only printing) : hexdump_scope.
Notation "'ab'" := (Byte.xab) (only printing) : hexdump_scope.
Notation "'ac'" := (Byte.xac) (only printing) : hexdump_scope.
Notation "'ad'" := (Byte.xad) (only printing) : hexdump_scope.
Notation "'ae'" := (Byte.xae) (only printing) : hexdump_scope.
Notation "'af'" := (Byte.xaf) (only printing) : hexdump_scope.
Notation "'b0'" := (Byte.xb0) (only printing) : hexdump_scope.
Notation "'b1'" := (Byte.xb1) (only printing) : hexdump_scope.
Notation "'b2'" := (Byte.xb2) (only printing) : hexdump_scope.
Notation "'b3'" := (Byte.xb3) (only printing) : hexdump_scope.
Notation "'b4'" := (Byte.xb4) (only printing) : hexdump_scope.
Notation "'b5'" := (Byte.xb5) (only printing) : hexdump_scope.
Notation "'b6'" := (Byte.xb6) (only printing) : hexdump_scope.
Notation "'b7'" := (Byte.xb7) (only printing) : hexdump_scope.
Notation "'b8'" := (Byte.xb8) (only printing) : hexdump_scope.
Notation "'b9'" := (Byte.xb9) (only printing) : hexdump_scope.
Notation "'ba'" := (Byte.xba) (only printing) : hexdump_scope.
Notation "'bb'" := (Byte.xbb) (only printing) : hexdump_scope.
Notation "'bc'" := (Byte.xbc) (only printing) : hexdump_scope.
Notation "'bd'" := (Byte.xbd) (only printing) : hexdump_scope.
Notation "'be'" := (Byte.xbe) (only printing) : hexdump_scope.
Notation "'bf'" := (Byte.xbf) (only printing) : hexdump_scope.
Notation "'c0'" := (Byte.xc0) (only printing) : hexdump_scope.
Notation "'c1'" := (Byte.xc1) (only printing) : hexdump_scope.
Notation "'c2'" := (Byte.xc2) (only printing) : hexdump_scope.
Notation "'c3'" := (Byte.xc3) (only printing) : hexdump_scope.
Notation "'c4'" := (Byte.xc4) (only printing) : hexdump_scope.
Notation "'c5'" := (Byte.xc5) (only printing) : hexdump_scope.
Notation "'c6'" := (Byte.xc6) (only printing) : hexdump_scope.
Notation "'c7'" := (Byte.xc7) (only printing) : hexdump_scope.
Notation "'c8'" := (Byte.xc8) (only printing) : hexdump_scope.
Notation "'c9'" := (Byte.xc9) (only printing) : hexdump_scope.
Notation "'ca'" := (Byte.xca) (only printing) : hexdump_scope.
Notation "'cb'" := (Byte.xcb) (only printing) : hexdump_scope.
Notation "'cc'" := (Byte.xcc) (only printing) : hexdump_scope.
Notation "'cd'" := (Byte.xcd) (only printing) : hexdump_scope.
Notation "'ce'" := (Byte.xce) (only printing) : hexdump_scope.
Notation "'cf'" := (Byte.xcf) (only printing) : hexdump_scope.
Notation "'d0'" := (Byte.xd0) (only printing) : hexdump_scope.
Notation "'d1'" := (Byte.xd1) (only printing) : hexdump_scope.
Notation "'d2'" := (Byte.xd2) (only printing) : hexdump_scope.
Notation "'d3'" := (Byte.xd3) (only printing) : hexdump_scope.
Notation "'d4'" := (Byte.xd4) (only printing) : hexdump_scope.
Notation "'d5'" := (Byte.xd5) (only printing) : hexdump_scope.
Notation "'d6'" := (Byte.xd6) (only printing) : hexdump_scope.
Notation "'d7'" := (Byte.xd7) (only printing) : hexdump_scope.
Notation "'d8'" := (Byte.xd8) (only printing) : hexdump_scope.
Notation "'d9'" := (Byte.xd9) (only printing) : hexdump_scope.
Notation "'da'" := (Byte.xda) (only printing) : hexdump_scope.
Notation "'db'" := (Byte.xdb) (only printing) : hexdump_scope.
Notation "'dc'" := (Byte.xdc) (only printing) : hexdump_scope.
Notation "'dd'" := (Byte.xdd) (only printing) : hexdump_scope.
Notation "'de'" := (Byte.xde) (only printing) : hexdump_scope.
Notation "'df'" := (Byte.xdf) (only printing) : hexdump_scope.
Notation "'e0'" := (Byte.xe0) (only printing) : hexdump_scope.
Notation "'e1'" := (Byte.xe1) (only printing) : hexdump_scope.
Notation "'e2'" := (Byte.xe2) (only printing) : hexdump_scope.
Notation "'e3'" := (Byte.xe3) (only printing) : hexdump_scope.
Notation "'e4'" := (Byte.xe4) (only printing) : hexdump_scope.
Notation "'e5'" := (Byte.xe5) (only printing) : hexdump_scope.
Notation "'e6'" := (Byte.xe6) (only printing) : hexdump_scope.
Notation "'e7'" := (Byte.xe7) (only printing) : hexdump_scope.
Notation "'e8'" := (Byte.xe8) (only printing) : hexdump_scope.
Notation "'e9'" := (Byte.xe9) (only printing) : hexdump_scope.
Notation "'ea'" := (Byte.xea) (only printing) : hexdump_scope.
Notation "'eb'" := (Byte.xeb) (only printing) : hexdump_scope.
Notation "'ec'" := (Byte.xec) (only printing) : hexdump_scope.
Notation "'ed'" := (Byte.xed) (only printing) : hexdump_scope.
Notation "'ee'" := (Byte.xee) (only printing) : hexdump_scope.
Notation "'ef'" := (Byte.xef) (only printing) : hexdump_scope.
Notation "'f0'" := (Byte.xf0) (only printing) : hexdump_scope.
Notation "'f1'" := (Byte.xf1) (only printing) : hexdump_scope.
Notation "'f2'" := (Byte.xf2) (only printing) : hexdump_scope.
Notation "'f3'" := (Byte.xf3) (only printing) : hexdump_scope.
Notation "'f4'" := (Byte.xf4) (only printing) : hexdump_scope.
Notation "'f5'" := (Byte.xf5) (only printing) : hexdump_scope.
Notation "'f6'" := (Byte.xf6) (only printing) : hexdump_scope.
Notation "'f7'" := (Byte.xf7) (only printing) : hexdump_scope.
Notation "'f8'" := (Byte.xf8) (only printing) : hexdump_scope.
Notation "'f9'" := (Byte.xf9) (only printing) : hexdump_scope.
Notation "'fa'" := (Byte.xfa) (only printing) : hexdump_scope.
Notation "'fb'" := (Byte.xfb) (only printing) : hexdump_scope.
Notation "'fc'" := (Byte.xfc) (only printing) : hexdump_scope.
Notation "'fd'" := (Byte.xfd) (only printing) : hexdump_scope.
Notation "'fe'" := (Byte.xfe) (only printing) : hexdump_scope.
Notation "'ff'" := (Byte.xff) (only printing) : hexdump_scope.

Local Open Scope hexdump_scope.
Goal False.
  let c := constr:(cons Byte.xba (cons Byte.xd1 (cons Byte.xde (cons Byte.xa5 nil)))) in
  let f := eval cbv in (c++c++c++c++c++c++c++c++c++c++c++c++c++c++c++c++c++Byte.xa1::nil)%list in
  idtac (*f*).
Abort.
