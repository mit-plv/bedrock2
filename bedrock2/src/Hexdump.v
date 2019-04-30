Require Import bedrock2.Byte.

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

Delimit Scope hexdump_scope with hexdump.

Notation "" := (@nil byte) (only printing, right associativity, at level 3) : hexdump_scope.
Notation "a b" :=
  (@cons byte a%hexdump b%hexdump)
  (only printing, right associativity, at level 3, format "a b")
  : hexdump_scope.
Notation "a b c d xs" :=
  (@cons byte a%hexdump (b%hexdump::c%hexdump::d%hexdump::xs%hexdump))%list
  (only printing, right associativity, at level 3, format "a  b  c  d   xs")
  : hexdump_scope.
Notation "x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 xs" := 
  (@cons byte x1%hexdump (x2%hexdump::x3%hexdump::x4%hexdump::x5%hexdump::x6%hexdump::x7%hexdump::x8%hexdump::x9%hexdump::x10%hexdump::x11%hexdump::x12%hexdump::x13%hexdump::x14%hexdump::x15%hexdump::x16%hexdump::x17%hexdump::x18%hexdump::x19%hexdump::x20%hexdump::x21%hexdump::x22%hexdump::x23%hexdump::x24%hexdump::x25%hexdump::x26%hexdump::x27%hexdump::x28%hexdump::x29%hexdump::x30%hexdump::x31%hexdump::x32%hexdump::xs%hexdump))%list
  (only printing, right associativity, at level 3, format "x1  x2  x3  x4   x5  x6  x7  x8   x9  x10  x11  x12   x13  x14  x15  x16   x17  x18  x19  x20   x21  x22  x23  x24   x25  x26  x27  x28   x29  x30  x31  x32 '//' xs")
  : hexdump_scope.

Undelimit Scope hexdump_scope.

Notation "'00'" := (x00) (only printing) : hexdump_scope.
Notation "'01'" := (x01) (only printing) : hexdump_scope.
Notation "'02'" := (x02) (only printing) : hexdump_scope.
Notation "'03'" := (x03) (only printing) : hexdump_scope.
Notation "'04'" := (x04) (only printing) : hexdump_scope.
Notation "'05'" := (x05) (only printing) : hexdump_scope.
Notation "'06'" := (x06) (only printing) : hexdump_scope.
Notation "'07'" := (x07) (only printing) : hexdump_scope.
Notation "'08'" := (x08) (only printing) : hexdump_scope.
Notation "'09'" := (x09) (only printing) : hexdump_scope.
Notation "'0a'" := (x0a) (only printing) : hexdump_scope.
Notation "'0b'" := (x0b) (only printing) : hexdump_scope.
Notation "'0c'" := (x0c) (only printing) : hexdump_scope.
Notation "'0d'" := (x0d) (only printing) : hexdump_scope.
Notation "'0e'" := (x0e) (only printing) : hexdump_scope.
Notation "'0f'" := (x0f) (only printing) : hexdump_scope.
Notation "'10'" := (x10) (only printing) : hexdump_scope.
Notation "'11'" := (x11) (only printing) : hexdump_scope.
Notation "'12'" := (x12) (only printing) : hexdump_scope.
Notation "'13'" := (x13) (only printing) : hexdump_scope.
Notation "'14'" := (x14) (only printing) : hexdump_scope.
Notation "'15'" := (x15) (only printing) : hexdump_scope.
Notation "'16'" := (x16) (only printing) : hexdump_scope.
Notation "'17'" := (x17) (only printing) : hexdump_scope.
Notation "'18'" := (x18) (only printing) : hexdump_scope.
Notation "'19'" := (x19) (only printing) : hexdump_scope.
Notation "'1a'" := (x1a) (only printing) : hexdump_scope.
Notation "'1b'" := (x1b) (only printing) : hexdump_scope.
Notation "'1c'" := (x1c) (only printing) : hexdump_scope.
Notation "'1d'" := (x1d) (only printing) : hexdump_scope.
Notation "'1e'" := (x1e) (only printing) : hexdump_scope.
Notation "'1f'" := (x1f) (only printing) : hexdump_scope.
Notation "'20'" := (x20) (only printing) : hexdump_scope.
Notation "'21'" := (x21) (only printing) : hexdump_scope.
Notation "'22'" := (x22) (only printing) : hexdump_scope.
Notation "'23'" := (x23) (only printing) : hexdump_scope.
Notation "'24'" := (x24) (only printing) : hexdump_scope.
Notation "'25'" := (x25) (only printing) : hexdump_scope.
Notation "'26'" := (x26) (only printing) : hexdump_scope.
Notation "'27'" := (x27) (only printing) : hexdump_scope.
Notation "'28'" := (x28) (only printing) : hexdump_scope.
Notation "'29'" := (x29) (only printing) : hexdump_scope.
Notation "'2a'" := (x2a) (only printing) : hexdump_scope.
Notation "'2b'" := (x2b) (only printing) : hexdump_scope.
Notation "'2c'" := (x2c) (only printing) : hexdump_scope.
Notation "'2d'" := (x2d) (only printing) : hexdump_scope.
Notation "'2e'" := (x2e) (only printing) : hexdump_scope.
Notation "'2f'" := (x2f) (only printing) : hexdump_scope.
Notation "'30'" := (x30) (only printing) : hexdump_scope.
Notation "'31'" := (x31) (only printing) : hexdump_scope.
Notation "'32'" := (x32) (only printing) : hexdump_scope.
Notation "'33'" := (x33) (only printing) : hexdump_scope.
Notation "'34'" := (x34) (only printing) : hexdump_scope.
Notation "'35'" := (x35) (only printing) : hexdump_scope.
Notation "'36'" := (x36) (only printing) : hexdump_scope.
Notation "'37'" := (x37) (only printing) : hexdump_scope.
Notation "'38'" := (x38) (only printing) : hexdump_scope.
Notation "'39'" := (x39) (only printing) : hexdump_scope.
Notation "'3a'" := (x3a) (only printing) : hexdump_scope.
Notation "'3b'" := (x3b) (only printing) : hexdump_scope.
Notation "'3c'" := (x3c) (only printing) : hexdump_scope.
Notation "'3d'" := (x3d) (only printing) : hexdump_scope.
Notation "'3e'" := (x3e) (only printing) : hexdump_scope.
Notation "'3f'" := (x3f) (only printing) : hexdump_scope.
Notation "'40'" := (x40) (only printing) : hexdump_scope.
Notation "'41'" := (x41) (only printing) : hexdump_scope.
Notation "'42'" := (x42) (only printing) : hexdump_scope.
Notation "'43'" := (x43) (only printing) : hexdump_scope.
Notation "'44'" := (x44) (only printing) : hexdump_scope.
Notation "'45'" := (x45) (only printing) : hexdump_scope.
Notation "'46'" := (x46) (only printing) : hexdump_scope.
Notation "'47'" := (x47) (only printing) : hexdump_scope.
Notation "'48'" := (x48) (only printing) : hexdump_scope.
Notation "'49'" := (x49) (only printing) : hexdump_scope.
Notation "'4a'" := (x4a) (only printing) : hexdump_scope.
Notation "'4b'" := (x4b) (only printing) : hexdump_scope.
Notation "'4c'" := (x4c) (only printing) : hexdump_scope.
Notation "'4d'" := (x4d) (only printing) : hexdump_scope.
Notation "'4e'" := (x4e) (only printing) : hexdump_scope.
Notation "'4f'" := (x4f) (only printing) : hexdump_scope.
Notation "'50'" := (x50) (only printing) : hexdump_scope.
Notation "'51'" := (x51) (only printing) : hexdump_scope.
Notation "'52'" := (x52) (only printing) : hexdump_scope.
Notation "'53'" := (x53) (only printing) : hexdump_scope.
Notation "'54'" := (x54) (only printing) : hexdump_scope.
Notation "'55'" := (x55) (only printing) : hexdump_scope.
Notation "'56'" := (x56) (only printing) : hexdump_scope.
Notation "'57'" := (x57) (only printing) : hexdump_scope.
Notation "'58'" := (x58) (only printing) : hexdump_scope.
Notation "'59'" := (x59) (only printing) : hexdump_scope.
Notation "'5a'" := (x5a) (only printing) : hexdump_scope.
Notation "'5b'" := (x5b) (only printing) : hexdump_scope.
Notation "'5c'" := (x5c) (only printing) : hexdump_scope.
Notation "'5d'" := (x5d) (only printing) : hexdump_scope.
Notation "'5e'" := (x5e) (only printing) : hexdump_scope.
Notation "'5f'" := (x5f) (only printing) : hexdump_scope.
Notation "'60'" := (x60) (only printing) : hexdump_scope.
Notation "'61'" := (x61) (only printing) : hexdump_scope.
Notation "'62'" := (x62) (only printing) : hexdump_scope.
Notation "'63'" := (x63) (only printing) : hexdump_scope.
Notation "'64'" := (x64) (only printing) : hexdump_scope.
Notation "'65'" := (x65) (only printing) : hexdump_scope.
Notation "'66'" := (x66) (only printing) : hexdump_scope.
Notation "'67'" := (x67) (only printing) : hexdump_scope.
Notation "'68'" := (x68) (only printing) : hexdump_scope.
Notation "'69'" := (x69) (only printing) : hexdump_scope.
Notation "'6a'" := (x6a) (only printing) : hexdump_scope.
Notation "'6b'" := (x6b) (only printing) : hexdump_scope.
Notation "'6c'" := (x6c) (only printing) : hexdump_scope.
Notation "'6d'" := (x6d) (only printing) : hexdump_scope.
Notation "'6e'" := (x6e) (only printing) : hexdump_scope.
Notation "'6f'" := (x6f) (only printing) : hexdump_scope.
Notation "'70'" := (x70) (only printing) : hexdump_scope.
Notation "'71'" := (x71) (only printing) : hexdump_scope.
Notation "'72'" := (x72) (only printing) : hexdump_scope.
Notation "'73'" := (x73) (only printing) : hexdump_scope.
Notation "'74'" := (x74) (only printing) : hexdump_scope.
Notation "'75'" := (x75) (only printing) : hexdump_scope.
Notation "'76'" := (x76) (only printing) : hexdump_scope.
Notation "'77'" := (x77) (only printing) : hexdump_scope.
Notation "'78'" := (x78) (only printing) : hexdump_scope.
Notation "'79'" := (x79) (only printing) : hexdump_scope.
Notation "'7a'" := (x7a) (only printing) : hexdump_scope.
Notation "'7b'" := (x7b) (only printing) : hexdump_scope.
Notation "'7c'" := (x7c) (only printing) : hexdump_scope.
Notation "'7d'" := (x7d) (only printing) : hexdump_scope.
Notation "'7e'" := (x7e) (only printing) : hexdump_scope.
Notation "'7f'" := (x7f) (only printing) : hexdump_scope.
Notation "'80'" := (x80) (only printing) : hexdump_scope.
Notation "'81'" := (x81) (only printing) : hexdump_scope.
Notation "'82'" := (x82) (only printing) : hexdump_scope.
Notation "'83'" := (x83) (only printing) : hexdump_scope.
Notation "'84'" := (x84) (only printing) : hexdump_scope.
Notation "'85'" := (x85) (only printing) : hexdump_scope.
Notation "'86'" := (x86) (only printing) : hexdump_scope.
Notation "'87'" := (x87) (only printing) : hexdump_scope.
Notation "'88'" := (x88) (only printing) : hexdump_scope.
Notation "'89'" := (x89) (only printing) : hexdump_scope.
Notation "'8a'" := (x8a) (only printing) : hexdump_scope.
Notation "'8b'" := (x8b) (only printing) : hexdump_scope.
Notation "'8c'" := (x8c) (only printing) : hexdump_scope.
Notation "'8d'" := (x8d) (only printing) : hexdump_scope.
Notation "'8e'" := (x8e) (only printing) : hexdump_scope.
Notation "'8f'" := (x8f) (only printing) : hexdump_scope.
Notation "'90'" := (x90) (only printing) : hexdump_scope.
Notation "'91'" := (x91) (only printing) : hexdump_scope.
Notation "'92'" := (x92) (only printing) : hexdump_scope.
Notation "'93'" := (x93) (only printing) : hexdump_scope.
Notation "'94'" := (x94) (only printing) : hexdump_scope.
Notation "'95'" := (x95) (only printing) : hexdump_scope.
Notation "'96'" := (x96) (only printing) : hexdump_scope.
Notation "'97'" := (x97) (only printing) : hexdump_scope.
Notation "'98'" := (x98) (only printing) : hexdump_scope.
Notation "'99'" := (x99) (only printing) : hexdump_scope.
Notation "'9a'" := (x9a) (only printing) : hexdump_scope.
Notation "'9b'" := (x9b) (only printing) : hexdump_scope.
Notation "'9c'" := (x9c) (only printing) : hexdump_scope.
Notation "'9d'" := (x9d) (only printing) : hexdump_scope.
Notation "'9e'" := (x9e) (only printing) : hexdump_scope.
Notation "'9f'" := (x9f) (only printing) : hexdump_scope.
Notation "'a0'" := (xa0) (only printing) : hexdump_scope.
Notation "'a1'" := (xa1) (only printing) : hexdump_scope.
Notation "'a2'" := (xa2) (only printing) : hexdump_scope.
Notation "'a3'" := (xa3) (only printing) : hexdump_scope.
Notation "'a4'" := (xa4) (only printing) : hexdump_scope.
Notation "'a5'" := (xa5) (only printing) : hexdump_scope.
Notation "'a6'" := (xa6) (only printing) : hexdump_scope.
Notation "'a7'" := (xa7) (only printing) : hexdump_scope.
Notation "'a8'" := (xa8) (only printing) : hexdump_scope.
Notation "'a9'" := (xa9) (only printing) : hexdump_scope.
Notation "'aa'" := (xaa) (only printing) : hexdump_scope.
Notation "'ab'" := (xab) (only printing) : hexdump_scope.
Notation "'ac'" := (xac) (only printing) : hexdump_scope.
Notation "'ad'" := (xad) (only printing) : hexdump_scope.
Notation "'ae'" := (xae) (only printing) : hexdump_scope.
Notation "'af'" := (xaf) (only printing) : hexdump_scope.
Notation "'b0'" := (xb0) (only printing) : hexdump_scope.
Notation "'b1'" := (xb1) (only printing) : hexdump_scope.
Notation "'b2'" := (xb2) (only printing) : hexdump_scope.
Notation "'b3'" := (xb3) (only printing) : hexdump_scope.
Notation "'b4'" := (xb4) (only printing) : hexdump_scope.
Notation "'b5'" := (xb5) (only printing) : hexdump_scope.
Notation "'b6'" := (xb6) (only printing) : hexdump_scope.
Notation "'b7'" := (xb7) (only printing) : hexdump_scope.
Notation "'b8'" := (xb8) (only printing) : hexdump_scope.
Notation "'b9'" := (xb9) (only printing) : hexdump_scope.
Notation "'ba'" := (xba) (only printing) : hexdump_scope.
Notation "'bb'" := (xbb) (only printing) : hexdump_scope.
Notation "'bc'" := (xbc) (only printing) : hexdump_scope.
Notation "'bd'" := (xbd) (only printing) : hexdump_scope.
Notation "'be'" := (xbe) (only printing) : hexdump_scope.
Notation "'bf'" := (xbf) (only printing) : hexdump_scope.
Notation "'c0'" := (xc0) (only printing) : hexdump_scope.
Notation "'c1'" := (xc1) (only printing) : hexdump_scope.
Notation "'c2'" := (xc2) (only printing) : hexdump_scope.
Notation "'c3'" := (xc3) (only printing) : hexdump_scope.
Notation "'c4'" := (xc4) (only printing) : hexdump_scope.
Notation "'c5'" := (xc5) (only printing) : hexdump_scope.
Notation "'c6'" := (xc6) (only printing) : hexdump_scope.
Notation "'c7'" := (xc7) (only printing) : hexdump_scope.
Notation "'c8'" := (xc8) (only printing) : hexdump_scope.
Notation "'c9'" := (xc9) (only printing) : hexdump_scope.
Notation "'ca'" := (xca) (only printing) : hexdump_scope.
Notation "'cb'" := (xcb) (only printing) : hexdump_scope.
Notation "'cc'" := (xcc) (only printing) : hexdump_scope.
Notation "'cd'" := (xcd) (only printing) : hexdump_scope.
Notation "'ce'" := (xce) (only printing) : hexdump_scope.
Notation "'cf'" := (xcf) (only printing) : hexdump_scope.
Notation "'d0'" := (xd0) (only printing) : hexdump_scope.
Notation "'d1'" := (xd1) (only printing) : hexdump_scope.
Notation "'d2'" := (xd2) (only printing) : hexdump_scope.
Notation "'d3'" := (xd3) (only printing) : hexdump_scope.
Notation "'d4'" := (xd4) (only printing) : hexdump_scope.
Notation "'d5'" := (xd5) (only printing) : hexdump_scope.
Notation "'d6'" := (xd6) (only printing) : hexdump_scope.
Notation "'d7'" := (xd7) (only printing) : hexdump_scope.
Notation "'d8'" := (xd8) (only printing) : hexdump_scope.
Notation "'d9'" := (xd9) (only printing) : hexdump_scope.
Notation "'da'" := (xda) (only printing) : hexdump_scope.
Notation "'db'" := (xdb) (only printing) : hexdump_scope.
Notation "'dc'" := (xdc) (only printing) : hexdump_scope.
Notation "'dd'" := (xdd) (only printing) : hexdump_scope.
Notation "'de'" := (xde) (only printing) : hexdump_scope.
Notation "'df'" := (xdf) (only printing) : hexdump_scope.
Notation "'e0'" := (xe0) (only printing) : hexdump_scope.
Notation "'e1'" := (xe1) (only printing) : hexdump_scope.
Notation "'e2'" := (xe2) (only printing) : hexdump_scope.
Notation "'e3'" := (xe3) (only printing) : hexdump_scope.
Notation "'e4'" := (xe4) (only printing) : hexdump_scope.
Notation "'e5'" := (xe5) (only printing) : hexdump_scope.
Notation "'e6'" := (xe6) (only printing) : hexdump_scope.
Notation "'e7'" := (xe7) (only printing) : hexdump_scope.
Notation "'e8'" := (xe8) (only printing) : hexdump_scope.
Notation "'e9'" := (xe9) (only printing) : hexdump_scope.
Notation "'ea'" := (xea) (only printing) : hexdump_scope.
Notation "'eb'" := (xeb) (only printing) : hexdump_scope.
Notation "'ec'" := (xec) (only printing) : hexdump_scope.
Notation "'ed'" := (xed) (only printing) : hexdump_scope.
Notation "'ee'" := (xee) (only printing) : hexdump_scope.
Notation "'ef'" := (xef) (only printing) : hexdump_scope.
Notation "'f0'" := (xf0) (only printing) : hexdump_scope.
Notation "'f1'" := (xf1) (only printing) : hexdump_scope.
Notation "'f2'" := (xf2) (only printing) : hexdump_scope.
Notation "'f3'" := (xf3) (only printing) : hexdump_scope.
Notation "'f4'" := (xf4) (only printing) : hexdump_scope.
Notation "'f5'" := (xf5) (only printing) : hexdump_scope.
Notation "'f6'" := (xf6) (only printing) : hexdump_scope.
Notation "'f7'" := (xf7) (only printing) : hexdump_scope.
Notation "'f8'" := (xf8) (only printing) : hexdump_scope.
Notation "'f9'" := (xf9) (only printing) : hexdump_scope.
Notation "'fa'" := (xfa) (only printing) : hexdump_scope.
Notation "'fb'" := (xfb) (only printing) : hexdump_scope.
Notation "'fc'" := (xfc) (only printing) : hexdump_scope.
Notation "'fd'" := (xfd) (only printing) : hexdump_scope.
Notation "'fe'" := (xfe) (only printing) : hexdump_scope.
Notation "'ff'" := (xff) (only printing) : hexdump_scope.

Local Open Scope hexdump_scope.
Goal False.
  let c := constr:(cons xba (cons xd1 (cons xde (cons xa5 nil)))) in
  let f := eval cbv in (c++c++c++c++c++c++c++c++c++c++c++c++c++c++c++c++c++xa1::nil)%list in
  idtac (*f*).
Abort.
