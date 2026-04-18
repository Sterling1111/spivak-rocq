From Lib Require Import Imports Tactics.

Ltac get_antiderivative g :=
  match goal with
  | |- context [ ∫ ?a ?b ?f ] =>
      let x := fresh "x" in
      let f_ast := match constr:(fun x : R => ltac:(
          let fx := eval cbv beta in (f x) in
          let e := reify_expr x fx in
          exact e
      )) with fun _ => ?e => e end in
      let E_name := fresh "E" in
      call_auto_int E_name f_ast;
      pose (g := fun x : R => eval_expr E_name x);
      cbv [E_name eval_expr] in g;
      clear E_name
  end.

Ltac auto_int_new :=
  match goal with
  | |- ∫ ?a ?b ?f = ?v =>
      let g := fresh "g" in
      get_antiderivative g;
      let f_name := fresh "f" in
      set (f_name := f);
      let H1 := fresh "H" in
      assert (H1 : a < b) by lra;
      let H2 := fresh "H" in
      assert (H2 : continuous_on f_name [a, b]); [ unfold f_name; auto_cont | ];
      let H3 := fresh "H" in
      assert (H3 : ⟦ der ⟧ g [a, b] = f_name) by (unfold f_name, g; auto_diff);
      let H_FTC := fresh "H_FTC" in
      pose proof (FTC2 a b f_name g H1 H2 H3) as H_FTC;
      rewrite H_FTC; unfold g; lra
  end.

Example FTC2_test_new : ∫ 0 1 (λ x : ℝ, 2 * x) = 1.
Proof.
  auto_int_new.
Qed.
