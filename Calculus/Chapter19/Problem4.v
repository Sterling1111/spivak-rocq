From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_4_i : forall c,
  ∫ (λ x, 1 / √(1 - x^2)) (-1, 1) = (λ x, arcsin x + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_4_ii : forall c,
  ∫ (λ x, √(1 - x^2)) (-1, 1) = (λ x, x * √(1 - x^2) / 2 + arcsin x / 2 + c).
Proof.
  intros c. unfold antiderivative_on. auto_diff. field_simplify.
  rewrite pow2_sqrt. field_simplify.
Admitted.

Lemma lemma_19_4_iii : forall c,
  ∫ (λ x, 1 / √(1 + x^2)) = (λ x, log (x + √(1 + x^2)) + c).
Proof.
  intros c. unfold antiderivative. auto_diff.
Admitted.

Lemma lemma_19_4_iv : forall c,
  ∫ (λ x, √(1 + x^2)) = (λ x, x * √(1 + x^2) / 2 + log (x + √(1 + x^2)) / 2 + c).
Proof.
  intros c. unfold antiderivative. auto_diff.
Admitted.
