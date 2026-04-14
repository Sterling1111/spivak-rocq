From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_20 : ∀ (f : R → R) (a : R),
  (∀ x, rational x → f x = x) →
  (∀ x, irrational x → f x = - x) →
  a ≠ 0 →
  ∀ L, ¬ (⟦ lim a ⟧ f = L).
Proof.
  intros f a H1 H2 H3 L H4.
  specialize (H4 (|a| / 3) ltac:(solve_R)) as [δ [H5 H6]].
  set (δ' := Rmin δ (|a| / 3)).
  destruct (exists_irrational_between a (a + δ') ltac:(unfold δ'; solve_R)) as [x [H7 H8]].
  destruct (exists_rational_between a (a + δ') ltac:(unfold δ'; solve_R)) as [y [H9 H10]].
  unfold δ' in *.
  specialize (H6 x ltac:(solve_R)) as H11.
  specialize (H6 y ltac:(solve_R)) as H12.
  rewrite H2 in H11; auto.
  rewrite H1 in H12; auto.
  solve_R.
Qed.
