Require Import bedrock2.Map bedrock2.Lift1Prop bedrock2.Map.Separation bedrock2.Map.SeparationLogic.

Section Example.
  Context {key value} {map : map key value} {ok : map.ok map}.
  Local Infix "*" := sep.

  Example separation_logic_automation A B C D E : exists R, impl1 (A*emp True*B*ex1(fun x:unit => C*(ex1 (fun v : value => (emp (x = x)* emp(v =v))*E v x)))*D) (A * ex1 (fun n => C * emp (1=n)) * R).
  Proof.
    normalize; try exact _.
    eexists ?[R].
    eapply impl1_ex1_r.
    eapply impl1_r_sep_emp.
    split. reflexivity.
    apply impl1_ex1_l. intros.
    apply impl1_ex1_l. intros.
    apply impl1_l_sep_emp. intros.
    cancel.
    (* packaging up the context: *)
    instantiate (1 := ex1 (fun x0 => ex1 (fun x => (B * (E x0 x * D))))).
    eapply impl1_ex1_r.
    eapply impl1_ex1_r.
    reflexivity.
  Qed.
End Example.