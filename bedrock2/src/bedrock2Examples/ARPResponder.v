Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry coqutil.Z.HexNotation.
Require Import bedrock2.FE310CSemantics.

Section WithParameters.
  Context {p : FE310CSemantics.parameters}.
  Import Syntax BinInt String List.ListNotations ZArith.
  Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
  Local Coercion expr.literal : Z >-> expr.
  Local Coercion expr.var : String.string >-> expr.
  Local Coercion name_of_func (f : function) : String.string := fst f.

Definition arp : bedrock_func :=
    let ethbuf : String.string := "ethbuf" in
    let buf : String.string := "buf" in
    let len : String.string := "len" in
  ("arp", ([ethbuf; len], [], bedrock_func_body:(
    require ( coq:(14+27) < len ) else { /*skip*/ };
    require ( (load1(ethbuf+coq:(14+0))== coq:(0))
            & (load1(ethbuf+coq:(14+1)) == coq:(1))
            & (load1(ethbuf+coq:(14+2)) == coq:(Ox"08"))
            & (load1(ethbuf+coq:(14+3)) == coq:(0))
            & (load1(ethbuf+coq:(14+4)) == coq:(6))
            & (load1(ethbuf+coq:(14+5)) == coq:(4))
            ) else { /*skip*/ };
    (* TODO: update sender mapping if present *)
    require ( (load1(ethbuf+coq:(14+6)) == coq:(0))
            & (load1(ethbuf+coq:(14+6+1)) == coq:(1))
            ) else { /*skip*/ }; (* request *)
    store1(ethbuf+coq:(14+6+1), coq:(2)); (* response *)
    (* TODO: add sender mapping to arp table *)

    (* dst := src *)
    store1(ethbuf+coq:(14+18  ), load1(ethbuf+coq:(14+8  )));
    store1(ethbuf+coq:(14+18+1), load1(ethbuf+coq:(14+8+1)));
    store1(ethbuf+coq:(14+18+2), load1(ethbuf+coq:(14+8+2)));
    store1(ethbuf+coq:(14+18+3), load1(ethbuf+coq:(14+8+3)));
    store1(ethbuf+coq:(14+18+4), load1(ethbuf+coq:(14+8+4)));
    store1(ethbuf+coq:(14+18+5), load1(ethbuf+coq:(14+8+5)));
    store1(ethbuf+coq:(14+18+6), load1(ethbuf+coq:(14+8+6)));
    store1(ethbuf+coq:(14+18+7), load1(ethbuf+coq:(14+8+7)));
    store1(ethbuf+coq:(14+18+8), load1(ethbuf+coq:(14+8+8)));
    store1(ethbuf+coq:(14+18+9), load1(ethbuf+coq:(14+8+9)));

    (* eth_dst = src *)
    store1(ethbuf           , load1(ethbuf+coq:(14+8  )));
    store1(ethbuf+coq:(1), load1(ethbuf+coq:(14+8+1)));
    store1(ethbuf+coq:(2), load1(ethbuf+coq:(14+8+2)));
    store1(ethbuf+coq:(3), load1(ethbuf+coq:(14+8+3)));
    store1(ethbuf+coq:(4), load1(ethbuf+coq:(14+8+4)));
    store1(ethbuf+coq:(5), load1(ethbuf+coq:(14+8+5)));

    (* src := me *)
    store1(ethbuf+coq:(14+8  ), coq:(Ox"f0"));
    store1(ethbuf+coq:(14+8+1), coq:(Ox"f1"));
    store1(ethbuf+coq:(14+8+2), coq:(Ox"f2"));
    store1(ethbuf+coq:(14+8+3), coq:(Ox"f3"));
    store1(ethbuf+coq:(14+8+4), coq:(Ox"f4"));
    store1(ethbuf+coq:(14+8+5), coq:(Ox"f5"));
    store1(ethbuf+coq:(14+8+6), coq:( 10));
    store1(ethbuf+coq:(14+8+7), coq:(155));
    store1(ethbuf+coq:(14+8+8), coq:(  5));
    store1(ethbuf+coq:(14+8+9), coq:(  1));

    (* eth_src = me *)
    store1(ethbuf+coq:(6+0), coq:(Ox"f0"));
    store1(ethbuf+coq:(6+1), coq:(Ox"f1"));
    store1(ethbuf+coq:(6+2), coq:(Ox"f2"));
    store1(ethbuf+coq:(6+3), coq:(Ox"f3"));
    store1(ethbuf+coq:(6+4), coq:(Ox"f4"));
    store1(ethbuf+coq:(6+5), coq:(Ox"f5"));

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
    require (coq:(14) < len) else { /*skip*/ } ;
    ethertype = (load1(buf + coq:(12)) << coq:(8)) | (load1(buf + coq:(13)));
    require (coq:(Ox"600"-1) < ethertype) else { /*skip*/ };
    if (ethertype == coq:(Ox"0800")) {
      ipv4(buf+coq:(14), len-coq:(14))
    } else if (ethertype == coq:(Ox"0806")) {
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
End WithParameters.
