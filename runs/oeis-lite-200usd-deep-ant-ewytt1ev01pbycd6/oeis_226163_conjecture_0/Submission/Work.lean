import FormalConjectures.Util.ProblemImports

open Matrix Nat Int Finset

namespace A226

/-! Scratch development for OEIS A226163 conjecture. -/

-- Character sum lemma (Lemma 1)
theorem char_sum_quadratic {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (β γ : F) :
    ∑ x : F, quadraticChar F (x^2 + β*x + γ) =
      if β^2 - 4*γ = 0 then (Fintype.card F : ℤ) - 1 else -1 := by
  sorry

end A226
