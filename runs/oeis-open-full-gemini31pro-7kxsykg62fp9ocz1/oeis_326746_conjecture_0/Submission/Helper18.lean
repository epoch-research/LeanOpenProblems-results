import Mathlib
import Submission.Helper10
import Submission.Helper16
import Submission.Helper17

lemma S_gt_C_tendsto (C : ℕ) :
  Filter.Tendsto (fun N : ℕ => ((List.range N).countP (fun q => S q ≤ C) : ℝ) / N) Filter.atTop (nhds 0) := by
  have hg : Filter.Tendsto (fun N : ℕ => (0 : ℝ)) Filter.atTop (nhds 0) := tendsto_const_nhds
  have hh := W_bound_tendsto_N C
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hg hh
  · intro N
    apply div_nonneg
    · positivity
    · positivity
  · intro N
    have h1 := countP_S_le_N C N
    have h2 : ((List.range N).countP (fun q => S q ≤ C) : ℝ) ≤ (((Nat.digits 10 N).length + 1)^C : ℕ) := by
      unfold f at h1
      exact_mod_cast h1
    have h3 : ((List.range N).countP (fun q => S q ≤ C) : ℝ) / N ≤ ((((Nat.digits 10 N).length + 1)^C : ℕ) : ℝ) / N := by
      apply div_le_div_of_nonneg_right h2
      positivity
    have h4 : (((((Nat.digits 10 N).length + 1)^C : ℕ) : ℝ) / N) = ((((Nat.digits 10 N).length + 1 : ℝ)^C) / N) := by
      congr 1
      exact_mod_cast rfl
    rw [h4] at h3
    exact h3

