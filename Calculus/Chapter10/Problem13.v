From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_13_a : ∀ f x,
  -1 < x < 1 ->
  f = (λ x, √ (1 - x^2)) ->
  ⟦ der x ⟧ f = (fun x => - x / √ (1 - x^2)).
Proof.
  intros f x H1 H2.
  subst.
  auto_diff.
Qed.

Lemma lemma_10_13_b : ∀ f a x,
  -1 < a < 1 ->
  f = (λ x, √ (1 - x^2)) ->
  x ≠ a -> f x ≠ f a + (- a / √ (1 - a^2)) * (x - a).
Proof. Abort.
