From Calculus.Chapter7 Require Import Prelude.

Lemma problem_7_9_a : ∀ f a,
  continuous f ->
  (∀ x, f x = 0 ↔ x = a) ->
  (∃ x1, x1 > a ∧ f x1 > 0) ->
  (∃ x2, x2 < a ∧ f x2 > 0) ->
  ∀ x, x ≠ a → f x > 0.
Proof.
  intros f a H1 H2 [x1 [H3 H4]] [x2 [H5 H6]] x H7.
  pose proof classic (f x > 0) as [H8 | H8]; auto.
  exfalso. apply Rnot_gt_le in H8.
  assert (H9 : f x < 0) by (assert (H10 : f x <> 0) by (intros H10; apply H2 in H10; lra); lra).
  assert (x > a \/ x < a) as [H10 | H10] by lra.
  - destruct (intermediate_value_theorem_unordered f x x1 0
     ltac:(apply continuous_imp_continuous_on; auto) ltac:(solve_R)) as [c [H11 H12]].
    apply H2 in H12. solve_R.
  - destruct (intermediate_value_theorem_unordered f x x2 0
     ltac:(apply continuous_imp_continuous_on; auto) ltac:(solve_R)) as [c [H11 H12]].
    apply H2 in H12. solve_R.
Qed.

Lemma problem_7_9_b : ∀ f a,
  continuous f ->
  (∀ x, f x = 0 ↔ x = a) ->
  (∃ x1, x1 > a ∧ f x1 > 0) ->
  (∃ x2, x2 < a ∧ f x2 < 0) ->
  (∀ x, x > a → f x > 0) ∧ (∀ x, x < a → f x < 0).
Proof.
  intros f a H1 H2 [x1 [H3 H4]] [x2 [H5 H6]].
  split.
  - intros x H7. pose proof classic (f x > 0) as [H8 | H8]; auto.
    exfalso. apply Rnot_gt_le in H8.
    assert (H9 : f x < 0) by (assert (H10 : f x <> 0) by (intros H10; apply H2 in H10; lra); lra).
    destruct (intermediate_value_theorem_unordered f x x1 0 
      ltac:(apply continuous_imp_continuous_on; auto) ltac:(solve_R)) as [c [H11 H12]].
    apply H2 in H12. subst c. solve_R.
  - intros x H7. pose proof classic (f x < 0) as [H8 | H8]; auto.
    exfalso. apply Rnot_lt_ge in H8.
    assert (H9 : f x > 0) by (assert (H10 : f x <> 0) by (intros H10; apply H2 in H10; lra); lra).
    destruct (intermediate_value_theorem_unordered f x x2 0 
      ltac:(apply continuous_imp_continuous_on; auto) ltac:(solve_R)) as [c [H11 H12]].
    apply H2 in H12. subst c. solve_R.
Qed.

Lemma problem_7_9_c : ∀ x y,
  x ≠ 0 ∨ y ≠ 0 ->
  (x^3 + x^2 * y + x * y^2 + y^3 > 0 ↔ x + y > 0) ∧
  (x^3 + x^2 * y + x * y^2 + y^3 < 0 ↔ x + y < 0).
Proof.
  intros x y H1.
  assert (H2 : x^3 + x^2 * y + x * y^2 + y^3 = (x^2 + y^2) * (x + y)) by nra.
  assert (H3 : x^2 + y^2 > 0) by nra.
  rewrite H2. split; split; intros H4; nra.
Qed.