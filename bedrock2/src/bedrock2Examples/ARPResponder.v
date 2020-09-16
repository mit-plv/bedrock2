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
    require ( constr:(14+27) < len ) else { /*skip*/ };
    require ( (load1(ethbuf+constr:(14+0))== constr:(0))
            & (load1(ethbuf+constr:(14+1)) == constr:(1))
            & (load1(ethbuf+constr:(14+2)) == constr:(Ox"08"))
            & (load1(ethbuf+constr:(14+3)) == constr:(0))
            & (load1(ethbuf+constr:(14+4)) == constr:(6))
            & (load1(ethbuf+constr:(14+5)) == constr:(4))
            ) else { /*skip*/ };
    (* TODO: update sender mapping if present *)
    require ( (load1(ethbuf+constr:(14+6)) == constr:(0))
            & (load1(ethbuf+constr:(14+6+1)) == constr:(1))
            ) else { /*skip*/ }; (* request *)
    store1(ethbuf+constr:(14+6+1), constr:(2)); (* response *)
    (* TODO: add sender mapping to arp table *)

    (* dst := src *)
    store1(ethbuf+constr:(14+18  ), load1(ethbuf+constr:(14+8  )));
    store1(ethbuf+constr:(14+18+1), load1(ethbuf+constr:(14+8+1)));
    store1(ethbuf+constr:(14+18+2), load1(ethbuf+constr:(14+8+2)));
    store1(ethbuf+constr:(14+18+3), load1(ethbuf+constr:(14+8+3)));
    store1(ethbuf+constr:(14+18+4), load1(ethbuf+constr:(14+8+4)));
    store1(ethbuf+constr:(14+18+5), load1(ethbuf+constr:(14+8+5)));
    store1(ethbuf+constr:(14+18+6), load1(ethbuf+constr:(14+8+6)));
    store1(ethbuf+constr:(14+18+7), load1(ethbuf+constr:(14+8+7)));
    store1(ethbuf+constr:(14+18+8), load1(ethbuf+constr:(14+8+8)));
    store1(ethbuf+constr:(14+18+9), load1(ethbuf+constr:(14+8+9)));

    (* eth_dst = src *)
    store1(ethbuf           , load1(ethbuf+constr:(14+8  )));
    store1(ethbuf+constr:(1), load1(ethbuf+constr:(14+8+1)));
    store1(ethbuf+constr:(2), load1(ethbuf+constr:(14+8+2)));
    store1(ethbuf+constr:(3), load1(ethbuf+constr:(14+8+3)));
    store1(ethbuf+constr:(4), load1(ethbuf+constr:(14+8+4)));
    store1(ethbuf+constr:(5), load1(ethbuf+constr:(14+8+5)));

    (* src := me *)
    store1(ethbuf+constr:(14+8  ), constr:(Ox"f0"));
    store1(ethbuf+constr:(14+8+1), constr:(Ox"f1"));
    store1(ethbuf+constr:(14+8+2), constr:(Ox"f2"));
    store1(ethbuf+constr:(14+8+3), constr:(Ox"f3"));
    store1(ethbuf+constr:(14+8+4), constr:(Ox"f4"));
    store1(ethbuf+constr:(14+8+5), constr:(Ox"f5"));
    store1(ethbuf+constr:(14+8+6), constr:( 10));
    store1(ethbuf+constr:(14+8+7), constr:(155));
    store1(ethbuf+constr:(14+8+8), constr:(  5));
    store1(ethbuf+constr:(14+8+9), constr:(  1));

    (* eth_src = me *)
    store1(ethbuf+constr:(6+0), constr:(Ox"f0"));
    store1(ethbuf+constr:(6+1), constr:(Ox"f1"));
    store1(ethbuf+constr:(6+2), constr:(Ox"f2"));
    store1(ethbuf+constr:(6+3), constr:(Ox"f3"));
    store1(ethbuf+constr:(6+4), constr:(Ox"f4"));
    store1(ethbuf+constr:(6+5), constr:(Ox"f5"));

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
    require (constr:(14) < len) else { /*skip*/ } ;
    ethertype = (load1(buf + constr:(12)) << constr:(8)) | (load1(buf + constr:(13)));
    require (constr:(Ox"600"-1) < ethertype) else { /*skip*/ };
    if (ethertype == constr:(Ox"0800")) {
      ipv4(buf+constr:(14), len-constr:(14))
    } else if (ethertype == constr:(Ox"0806")) {
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
