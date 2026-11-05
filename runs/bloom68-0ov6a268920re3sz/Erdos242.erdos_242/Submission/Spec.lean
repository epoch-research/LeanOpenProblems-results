import FormalConjecturesUtil

/-!
# Erdős Problem 242

*References:*
- [erdosproblems.com/242](https://www.erdosproblems.com/242)
- [Si56] Sierpiński, W., Sur les décompositions de nombres rationnels en fractions primaires.
  Mathesis (1956), 16--32.
-/

open scoped Topology

namespace Erdos242

/--
For every $n>2$ there exist distinct integers $1 ≤ x < y < z$
such that $\frac 4 n = \frac 1 x + \frac 1 y + \frac 1 z$.
-/
theorem erdos_242 (n : ℕ) (hn : 2 < n) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (4 / n : ℚ) = 1 / x + 1 / y + 1 / z := by
  sorry

end Erdos242

theorem Erdos242.erdos_242.disproof : ¬ (type_of% @Erdos242.erdos_242) := sorry
