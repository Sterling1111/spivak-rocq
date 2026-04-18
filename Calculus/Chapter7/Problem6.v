From Calculus.Chapter7 Require Import Prelude.

Lemma lemma_7_6 : ∀ f,
  continuous_on f [-1, 1] ->
  (∀ x, x ∈ [-1, 1] -> x^2 + (f x)^2 = 1) ->
  (∀ x, x ∈ [-1, 1] -> f x = √(1 - x^2)) \/
  (∀ x, x ∈ [-1, 1] -> f x = -√(1 - x^2)).
Proof.
  intros f H1 H2. 
  pose proof classic ((∀ x : ℝ, x ∈ [-1, 1] → f x = √(1 - x ^ 2)) ∨ ∀ x : ℝ, x ∈ [-1, 1] → f x = - √(1 - x ^ 2)) as [H3 | H3]; auto.
  exfalso.
  apply not_or_and in H3 as [H3 H4].
  apply not_all_ex_not in H3 as [x H5].
  apply not_all_ex_not in H4 as [y H6].
  apply imply_to_and in H5 as [H5 H7].
  apply imply_to_and in H6 as [H8 H9].

  assert (H10 : ∀ z, z ∈ [-1, 1] → f z = √(1 - z ^ 2) \/ f z = - √(1 - z ^ 2)).
  {
    intros z H10. apply H2 in H10.
    assert (H11 : (f z) ^ 2 = (√(1 - z ^ 2)) ^ 2) by (rewrite pow2_sqrt; nra).
    nra.
  }

  destruct (H10 x H5) as [H11 | H11]; try lra.
  destruct (H10 y H8) as [H12 | H12]; try lra.

  assert (H13 : x < 1 ∧ x > -1) by (specialize (H2 x H5); nra).
  assert (H14 : y < 1 ∧ y > -1) by (specialize (H2 y H8); nra).

  assert (H15 : f x < 0) by (pose proof (sqrt_pos (1 - x ^ 2)); lra).
  assert (H16 : f y > 0) by (pose proof (sqrt_pos (1 - y ^ 2)); lra).

  destruct (intermediate_value_theorem_unordered f x y 0 
    ltac:(eapply continuous_on_subset_closed; eauto; solve_R) ltac:(solve_R)) as [c [H17 H18]].
  assert (H19 : c ∈ [-1, 1]) by solve_R.
  apply H2 in H19.
  solve_R.
Qed.