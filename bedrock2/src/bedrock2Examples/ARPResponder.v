Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.FE310CSemantics.

Import Syntax BinInt String List.ListNotations ZArith.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition arp : bedrock_func :=
    let ethbuf : String.string := "ethbuf" in
    let buf : String.string := "buf" in
    let len : String.string := "len" in
  ("arp", ([ethbuf; len], [], bedrock_func_body:(
    require ( $(14+27) < len ) else { /*skip*/ };
    require ( (load1(ethbuf+$(14+0))== $0)
            & (load1(ethbuf+$(14+1)) == $1)
            & (load1(ethbuf+$(14+2)) == $0x08)
            & (load1(ethbuf+$(14+3)) == $0)
            & (load1(ethbuf+$(14+4)) == $6)
            & (load1(ethbuf+$(14+5)) == $4)
            ) else { /*skip*/ };
    (* TODO: update sender mapping if present *)
    require ( (load1(ethbuf+$(14+6)) == $0)
            & (load1(ethbuf+$(14+6+1)) == $1)
            ) else { /*skip*/ }; (* request *)
    store1(ethbuf+$(14+6+1), $2); (* response *)
    (* TODO: add sender mapping to arp table *)

    (* dst := src *)
    store1(ethbuf+$(14+18  ), load1(ethbuf+$(14+8  )));
    store1(ethbuf+$(14+18+1), load1(ethbuf+$(14+8+1)));
    store1(ethbuf+$(14+18+2), load1(ethbuf+$(14+8+2)));
    store1(ethbuf+$(14+18+3), load1(ethbuf+$(14+8+3)));
    store1(ethbuf+$(14+18+4), load1(ethbuf+$(14+8+4)));
    store1(ethbuf+$(14+18+5), load1(ethbuf+$(14+8+5)));
    store1(ethbuf+$(14+18+6), load1(ethbuf+$(14+8+6)));
    store1(ethbuf+$(14+18+7), load1(ethbuf+$(14+8+7)));
    store1(ethbuf+$(14+18+8), load1(ethbuf+$(14+8+8)));
    store1(ethbuf+$(14+18+9), load1(ethbuf+$(14+8+9)));

    (* eth_dst = src *)
    store1(ethbuf           , load1(ethbuf+$(14+8  )));
    store1(ethbuf+$1, load1(ethbuf+$(14+8+1)));
    store1(ethbuf+$2, load1(ethbuf+$(14+8+2)));
    store1(ethbuf+$3, load1(ethbuf+$(14+8+3)));
    store1(ethbuf+$4, load1(ethbuf+$(14+8+4)));
    store1(ethbuf+$5, load1(ethbuf+$(14+8+5)));

    (* src := me *)
    store1(ethbuf+$(14+8  ), $0xf0);
    store1(ethbuf+$(14+8+1), $0xf1);
    store1(ethbuf+$(14+8+2), $0xf2);
    store1(ethbuf+$(14+8+3), $0xf3);
    store1(ethbuf+$(14+8+4), $0xf4);
    store1(ethbuf+$(14+8+5), $0xf5);
    store1(ethbuf+$(14+8+6), $ 10);
    store1(ethbuf+$(14+8+7), $155);
    store1(ethbuf+$(14+8+8), $  5);
    store1(ethbuf+$(14+8+9), $  1);

    (* eth_src = me *)
    store1(ethbuf+$(6+0), $0xf0);
    store1(ethbuf+$(6+1), $0xf1);
    store1(ethbuf+$(6+2), $0xf2);
    store1(ethbuf+$(6+3), $0xf3);
    store1(ethbuf+$(6+4), $0xf4);
    store1(ethbuf+$(6+5), $0xf5);

    /*skip*/
))).

Definition ipv4 : bedrock_func :=
    let buf : String.string := "buf" in
    let len : String.string := "len" in
  ("ipv4", ([buf; len], [], bedrock_func_body:(
    /*skip*/
))).

Definition ethernet : bedrock_func :=
    let ipv4 : String.string := "ipv4" in
    let arp : String.string := "arp" in
    let buf : String.string := "buf" in
    let len : String.string := "len" in
    let ethertype : String.string := "ethertype" in
  ("ethernet", ((buf::len::nil), @nil String.string, bedrock_func_body:(
    require ($14 < len) else { /*skip*/ } ;
    ethertype = (load1(buf + $12) << $8) | (load1(buf + $13));
    require ($(0x600-1) < ethertype) else { /*skip*/ };
    if (ethertype == $0x0800) {
      ipv4(buf+$14, len-$14)
    } else if (ethertype == $0x0806) {
      arp(buf, len)
    }
))).

Require Import bedrock2.ToCString.
Goal True.
  let c_code := eval cbv in ((c_module (ethernet::arp::ipv4::nil))) in
      idtac
        (*
        c_code
        *)
  .
Abort.
