import Mathlib
import Submission.Helper10

lemma W_bound_tendsto (C : ℕ) :
  Filter.Tendsto (fun k : ℕ => ((k + 1) ^ C : ℝ) / 10 ^ k) Filter.atTop (nhds 0) := by
  have h1 : 1 < (10 : ℝ) := by norm_num
  have h2 := tendsto_pow_const_div_const_pow_of_one_lt C h1
  have h3 : Filter.Tendsto (fun k : ℕ => k + 1) Filter.atTop Filter.atTop := Filter.tendsto_add_atTop_nat 1
  have h4 := Filter.Tendsto.comp h2 h3
  have h4' : Filter.Tendsto (fun k : ℕ => ((k + 1 : ℝ)^C) / 10^(k+1)) Filter.atTop (nhds 0) := by
    have eq : ((fun n : ℕ => (n : ℝ)^C / 10^n) ∘ fun k : ℕ => k + 1) = fun k : ℕ => ((k + 1 : ℝ)^C) / 10^(k+1) := by
      ext k
      simp
    rw [eq] at h4
    exact h4
  have h5 : Filter.Tendsto (fun k : ℕ => 10 * (((k + 1 : ℝ)^C) / 10^(k+1))) Filter.atTop (nhds (10 * 0)) := by
    apply Filter.Tendsto.const_mul 10
    exact h4'
  have h6 : (fun k : ℕ => 10 * (((k + 1 : ℝ)^C) / 10^(k+1))) = (fun k : ℕ => ((k + 1 : ℝ)^C) / 10^k) := by
    ext k
    simp [pow_succ']
    ring
  rw [←h6]
  simp at h5
  exact h5
