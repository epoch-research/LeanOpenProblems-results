import FormalConjectures.Util.ProblemImports

open Real Int

set_option pp.all true

theorem test_rw (n : ℕ) (q : ℤ) (h_q_gt : Real.pi * (10 : ℝ) ^ n < (q : ℝ))
    (h_q_lt : (q : ℝ) < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n)) :
    ∃ (k' : ℤ), Real.pi * (10 : ℝ) ^ n.cast < k'.cast ∧
      k'.cast < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n.cast) := by
  use q
  sorry
