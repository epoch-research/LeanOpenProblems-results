import FormalConjecturesUtil

/-!
# Erdős Problem 52

*Reference:* [erdosproblems.com/52](https://www.erdosproblems.com/52)
-/

open scoped Pointwise

namespace Erdos52

/--
Let $A$ be a finite set of integers. Is it true that for every $\epsilon>0$
$\max( \lvert A+A\rvert,\lvert AA\rvert)\gg_\epsilon \lvert A\rvert^{2-\epsilon}?$
-/
theorem erdos_52 : ∀ (ε : ℝ), 0 < ε → ε < 1 → ∃ (C : ℝ), 0 < C ∧ ∀ (A : Finset ℤ),
    (max (A + A).card (A * A).card : ℝ) ≥ C * (A.card : ℝ) ^ (2 - ε) := by
  sorry

-- TODO(firsching): Add additional material.

end Erdos52
