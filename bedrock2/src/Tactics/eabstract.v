Tactic Notation "eabstract" tactic3(tac) :=
  let G := match goal with |- ?G => G end in
  let pf := lazymatch constr:(ltac:(tac) : G) with ?pf => pf end in
  repeat match goal with
         | H: ?T |- _ => has_evar T;
                         clear dependent H;
                         assert_succeeds (pose pf)
         | H := ?e |- _ => has_evar e;
                         clear dependent H;
                         assert_succeeds (pose pf)
         end;
  abstract (exact_no_check pf).

Tactic Notation "tryabstract" tactic3(tac) :=
  let G := match goal with |- ?G => G end in
  unshelve (
      let pf := lazymatch open_constr:(ltac:(tac) : G) with ?pf => pf end in
      tryif has_evar pf
      then exact pf
      else eabstract exact_no_check pf);
  shelve_unifiable.
