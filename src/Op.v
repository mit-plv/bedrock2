Require Export bbv.Word.

Inductive binop: Set := OPlus | OMinus | OTimes | OEq | OLt | OAnd.

Definition eval_binop{w: nat}(op: binop)(v1 v2: word w): word w :=
  match op with
  | OPlus => v1 ^+ v2
  | OMinus => v1 ^- v2
  | OTimes => v1 ^* v2
  | OEq => if weq v1 v2 then wone w else wzero w
  | OLt => if wlt_dec v1 v2 then wone w else wzero w
  | OAnd => v1 ^& v2
  end.
