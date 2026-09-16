import Submission.Spec
open Nat Finset

lemma T_term_eq_choose (k : ℕ) : T_term k = (6*k).choose (3*k) * (3*k).choose k := rfl

theorem T_term_mul_T_term_div_D (k m : ℕ) :
  (2*(k+m) - 1) * (3*(k+m)).choose (k+m) ∣ T_term k * T_term m := by
  sorry
