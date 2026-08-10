import FormalConjectures.Util.ProblemImports

open scoped Real

noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

-- Target odd formula, as found computationally.
example (k : ℕ) :
    a (2 * k + 1) =
      ((4 : ℝ) ^ (6*k + 3) * (Nat.factorial (4*k+2) : ℝ) * (Nat.factorial (9*k+4) : ℝ)) /
      ((Nat.factorial (3*k+1) : ℝ) * (Nat.factorial (8*k+4) : ℝ) * (Nat.factorial (2*k+1) : ℝ)) := by
  unfold a
  ring_nf
  -- Need half-integer gamma evaluations:
  -- Gamma(9/2*(2k+1)+1)=Gamma(9k+11/2)=Gamma((9k+5)+1/2)
  -- Gamma(3/2*(2k+1)+1)=Gamma(3k+5/2)=Gamma((3k+2)+1/2)
  sorry
