import FormalConjectures.Util.ProblemImports

example (n : ℕ) (h : 1 ≤ n) : n * (n - 1) ≤ n ^ 2 - 1 := by
  cases n with
  | zero => omega
  | succ m =>
      simp only [Nat.succ_sub_one]
      rw [pow_two]
      have hcalc : (m + 1) * (m + 1) = (m + 1) * m + (m + 1) := by ring
      rw [hcalc]
      omega
