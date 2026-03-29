From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_1_i : forall c,
  ∫ (λ x, ((x ^^ (3 / 5)) + (x ^^ (1 / 6))) / √ x) =
  (λ x, 10 / 11 * (x ^^ (11 / 10)) + 3 / 2 * (x ^^ (2 / 3)) + c).
Proof.
  intros c. 
Admitted.

Lemma lemma_19_1_ii : forall c,
  ∫ (λ x, 1 / (√ (x - 1) + √ (x + 1))) =
  (λ x, 1 / 3 * ((x + 1) ^^ (3 / 2)) - 1 / 3 * ((x - 1) ^^ (3 / 2)) + c).
Proof.
 intros c. 
Admitted.

Lemma lemma_19_1_iii : forall c,
  ∫ (λ x, (exp x + exp (2 * x) + exp (3 * x)) / exp (4 * x)) =
  (λ x, -1 / 3 * exp (-3 * x) - 1 / 2 * exp (-2 * x) - exp (-x) + c).
Proof.
  intros c. unfold antiderivative. 
Admitted.

Lemma lemma_19_1_iv : forall a b c, a > 0 -> b > 0 -> a <> b ->
  ∫ (λ x, (a ^^ x) / (b ^^ x)) =
  (λ x, ((a / b) ^^ x) / log (a / b) + c).
Proof. Admitted.

Lemma lemma_19_1_v : forall c,
  ∫ (λ x, (tan x) ^ 2) = 
  (λ x, tan x - x + c).
Proof. Admitted.

Lemma lemma_19_1_vi : forall a c, a <> 0 ->
  ∫ (λ x, 1 / (a ^ 2 + x ^ 2)) =
  (λ x, 1 / a * arctan (x / a) + c).
Proof. Admitted.

Lemma lemma_19_1_vii : forall a c, a > 0 ->
  ∫ (λ x, 1 / √ (a ^ 2 - x ^ 2)) = 
  (λ x, arcsin (x / a) + c).
Proof. Admitted.

Lemma lemma_19_1_viii : forall c,
  ∫ (λ x, 1 / (1 + sin x)) = 
  (λ x, tan x - 1 / cos x + c).
Proof. Admitted.

Lemma lemma_19_1_ix : forall c,
  ∫ (λ x, (8 * x ^ 2 + 6 * x + 4) / (x + 1)) =
  (λ x, 4 * x ^ 2 - 2 * x + 6 * log (Rabs (x + 1)) + c).
Proof. Admitted.

Lemma lemma_19_1_x : forall c,
  ∫ (λ x, 1 / √ (2 * x - x ^ 2)) = 
  (λ x, arcsin (x - 1) + c).
Proof. Admitted.