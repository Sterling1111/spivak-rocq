From Lib Require Import Tactics.
Require Import Reals.
Open Scope R_scope.

Set Ltac Profiling.
Lemma test_int_sqrt_1 : ∫ 0 1 (λ x, sqrt x) = 2 / 3.
Proof.
  auto_int. pose proof sqrt_lt_R0 x ltac:(solve_R) as H1.
  pose proof (sqrt_sqrt x ltac:(solve_R)) as H2.
  apply Rmult_eq_reg_r with (r := 3 * √x); solve_R.
Qed.
Show Ltac Profile.
