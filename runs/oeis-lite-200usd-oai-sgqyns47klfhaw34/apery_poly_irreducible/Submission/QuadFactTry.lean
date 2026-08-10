import FormalConjectures.Util.ProblemImports
-- This should prove a true statement: no rational square is -1.
example (r : ℚ) : r ^ 2 ≠ (-1 : ℤ) + 0 * r := by
  haveI : Fact (Squarefree (-1:ℤ)) := ⟨by
    intro x hx
    -- x*x divides -1, so x is a unit
    exact Int.isUnit_iff.2 (by
      rcases hx with ⟨y, hy⟩
      have habs : (x.natAbs)^2 ∣ 1 := by
        use y.natAbs
        -- too tedious
        sorry)⟩
  haveI : Fact ((-1:ℤ) ≠ 1) := ⟨by norm_num⟩
  exact (QuadraticAlgebra.fact_field (d := -1)).out r
