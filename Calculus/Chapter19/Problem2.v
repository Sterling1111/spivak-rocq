From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_2_i : forall c,
  ∫ (λ x, (1 + x)^5) = (λ x, (1 + x)^6 / 6 + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_2_ii : forall c,
  ∫ (λ x, sin x * cos x) = (λ x, (sin x)^2 / 2 + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_2_iii : forall c,
  ∫ (λ x, exp (sin x) * cos x) = (λ x, exp (sin x) + c).
Proof.
  auto_int.
Qed.