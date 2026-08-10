import FormalConjectures.Util.ProblemImports

open Real Int

theorem test_rw (n : ℕ) (q : ℤ) (h_q_gt : Real.pi * (10 : ℝ) ^ n < (q : ℝ))
    (h_q_lt : (q : ℝ) < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n)) :
    ∃ (k' : ℤ), Real.pi * (10 : ℝ) ^ n.cast < k'.cast ∧
      k'.cast < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n.cast) := by
  use q
  exact ⟨h_q_gt, h_q_lt⟩
