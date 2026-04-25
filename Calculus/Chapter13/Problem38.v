From Calculus.Chapter13 Require Import Prelude.

Section section_13_38.

Variable a b : ℝ.
Variables f g : ℝ → ℝ.
Variable P : partition a b.

Let l : list R := P.(points a b).

Hypothesis H1: a <= b.
Hypothesis H2 : integrable_on a b f.
Hypothesis H3 : integrable_on a b g.
Hypothesis H4 : forall x, x ∈ [a, b] -> f x >= 0.
Hypothesis H5 : forall x, x ∈ [a, b] -> g x >= 0.

Let H6 : bounded_on f [a, b] := integrable_imp_bounded f a b H1 H2.
Let H7 : bounded_on g [a, b] := integrable_imp_bounded g a b H1 H3.
Let H8 : bounded_on (f ⋅ g) [a, b] := bounded_on_mult f g a b H6 H7.

Let M'_list := proj1_sig (partition_sublist_elem_has_sup f a b P H6).
Let m'_list := proj1_sig (partition_sublist_elem_has_inf f a b P H6).
Let M''_list := proj1_sig (partition_sublist_elem_has_sup g a b P H7).
Let m''_list := proj1_sig (partition_sublist_elem_has_inf g a b P H7).
Let M_list := proj1_sig (partition_sublist_elem_has_sup (f ⋅ g) a b P H8).
Let m_list := proj1_sig (partition_sublist_elem_has_inf (f ⋅ g) a b P H8).

Let M' := λ i, M'_list.[i].
Let m' := λ i, m'_list.[i].
Let M'' := λ i, M''_list.[i].
Let m'' := λ i, m''_list.[i].
Let M := λ i, M_list.[i].
Let m := λ i, m_list.[i].

Lemma partition_lists_lengths :
  length M'_list = (length l - 1)%nat /\
  length m'_list = (length l - 1)%nat /\
  length M''_list = (length l - 1)%nat /\
  length m''_list = (length l - 1)%nat /\
  length M_list = (length l - 1)%nat /\
  length m_list = (length l - 1)%nat.
Proof.
  repeat split.
  - exact (proj1 (proj2_sig (partition_sublist_elem_has_sup f a b P H6))).
  - exact (proj1 (proj2_sig (partition_sublist_elem_has_inf f a b P H6))).
  - exact (proj1 (proj2_sig (partition_sublist_elem_has_sup g a b P H7))).
  - exact (proj1 (proj2_sig (partition_sublist_elem_has_inf g a b P H7))).
  - exact (proj1 (proj2_sig (partition_sublist_elem_has_sup (f ⋅ g) a b P H8))).
  - exact (proj1 (proj2_sig (partition_sublist_elem_has_inf (f ⋅ g) a b P H8))).
Qed.

Lemma lemma_38_a : ∀ (i : ℕ),
  M i <= M' i * M'' i /\ m i >= m' i * m'' i.
Proof.
  intros i.
  assert ((i >= (length l - 1))%nat \/ (i < (length l - 1))%nat) as [H9 | H9] by lia.
  - unfold M, M', M'', m, m', m''. repeat rewrite nth_overflow; pose proof partition_lists_lengths; try lia; lra.
  - assert (∀ x, x ∈ [l.[i], l.[i+1]] -> (0 <= m' i <= f x <= M' i) /\ (0 <= m'' i <= g x <= M'' i)) as H10.
    { admit. }
    specialize (H10 (l.[i])). 
Admitted.
  


End section_13_38.

Lemma lemma_13_38_d : forall f g a b,
  a < b ->
  integrable_on a b f ->
  integrable_on a b g ->
  (forall x, x ∈ [a, b] -> f x >= 0) ->
  (forall x, x ∈ [a, b] -> g x >= 0) ->
  integrable_on a b (f ⋅ g).
Abort.

Lemma lemma_13_38_e : forall f g a b,
  a < b ->
  integrable_on a b f ->
  integrable_on a b g ->
  integrable_on a b (f ⋅ g).
Abort.
