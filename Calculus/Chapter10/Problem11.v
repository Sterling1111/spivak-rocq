From Calculus.Chapter10 Require Import Prelude.
From Calculus.Chapter5 Require Import Problem21.

Lemma lemma_10_11 : ∀ f g,
  (∀ x, x ≠ 0 -> f x = g x * sin (1 / x)) ->
  f 0 = 0 ->
  g 0 = 0 ->
  ⟦ der 0 ⟧ g = (λ x, 0) ->
  ⟦ der 0 ⟧ f = (λ x, 0).
Proof.
  intros f g H1 H2 H3 H4.
  unfold derivative_at in *.
  apply limit_eq with (f1 := λ x, (((1 / x) * g x) * (sin (1/x)))).
  { exists 1. split; [lra |]. intros x H5. rewrite H2, H1; simp_zero; solve_R. }
  apply lemma_5_21_b with (M := 1).
  - intros x. pose proof sin_bounds (1/x) as H5. solve_R.
  - apply limit_eq with (f1 := (λ h : ℝ, (g (0 + h) - g 0) / h)); auto.
    exists 1; split; [lra |].
    intros x H5. rewrite H3. simp_zero. solve_R.
Qed.