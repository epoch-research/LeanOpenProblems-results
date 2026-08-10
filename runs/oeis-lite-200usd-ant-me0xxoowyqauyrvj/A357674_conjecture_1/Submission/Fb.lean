import FormalConjectures.Util.ProblemImports
open Nat Finset BigOperators

/-- Faulhaber, isolating the lowest-order (`n^1`) term:
`∑_{k<p} k^m = bernoulli m * p + (higher order terms in p)`. -/
theorem sum_pow_eq_top_term (p m : ℕ) :
    (∑ k ∈ range p, (k:ℚ)^m)
      = bernoulli m * (p:ℚ)
        + ∑ i ∈ range m, bernoulli i * ((m+1).choose i) * (p:ℚ)^(m+1-i) / (m+1) := by
  rw [sum_range_pow, Finset.sum_range_succ]
  have hch : ((m+1).choose m : ℚ) = (m:ℚ)+1 := by
    rw [Nat.choose_succ_self_right]; push_cast; ring
  have h2 : bernoulli m * ((m+1).choose m) * (p:ℚ)^(m+1-m) / (m+1) = bernoulli m * p := by
    rw [hch, show m+1-m = 1 by omega, pow_one]
    have hm1 : (m:ℚ)+1 ≠ 0 := by positivity
    field_simp
  rw [h2]; ring
