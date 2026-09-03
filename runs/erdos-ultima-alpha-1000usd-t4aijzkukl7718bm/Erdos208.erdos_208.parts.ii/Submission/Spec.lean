import FormalConjecturesUtil

/-!
# Erdős Problem 208
*Reference:* [erdosproblems.com/208](https://www.erdosproblems.com/208)
-/

open Filter Real

namespace Erdos208

/-- The sequence of squarefree numbers, denoted by `s` as in Erdős problem 208. -/
noncomputable def erdos208.s : ℕ → ℕ := Nat.nth Squarefree

open erdos208

/--
Let $s_1 < s_2 < \dots$ be the sequence of squarefree numbers. Is it true that
$s_{n + 1} - s_n \le (1 + o(1)) \cdot (\pi^2 / 6) \cdot \log (s_n) / \log (\log (s_n))$?
-/
theorem erdos_208.parts.ii : ∃ (c : ℕ → ℝ), (c =o[atTop] (1 : ℕ → ℝ)) ∧ ∀ᶠ n in atTop,
      s (n + 1) - s n ≤ (1 + (c n)) * (π^2 / 6) * log (s n) / log (log (s n)) := by
  sorry

end Erdos208
