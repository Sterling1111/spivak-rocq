From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_19 : ∀ f a,
  (∀ x, irrational x → f x = 0) → (∀ x, rational x → f x = 1) → ∀ L, ¬ (⟦ lim a ⟧ f = L).
Proof.
  intros f a H1 H2 L H3.
  specialize (H3 (1/3) ltac:(lra)) as [δ [H4 H5]].
  destruct (exists_irrational_between a (a + δ) ltac:(lra)) as [x [H6 H7]].
  destruct (exists_rational_between a (a + δ) ltac:(lra)) as [y [H8 H9]].
  specialize (H5 x ltac:(solve_R)) as H10.
  specialize (H5 y ltac:(solve_R)) as H11.
  rewrite H1 in H10; auto.
  rewrite H2 in H11; auto.
  solve_R.
Qed.