From Calculus.Chapter19 Require Import Prelude.
Lemma test : exists C, forall x, x > 0 -> (∫ (λ x, x)) x = x^2 / 2 + C.
Admitted.
