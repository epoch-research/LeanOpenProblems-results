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
for any $\epsilon > 0$ and large $n$, $s_{n+1} - s_n \ll_\epsilon s_n^\epsilon$?
-/
theorem erdos_208.parts.i : 
    ∀ ε > (0 : ℝ), (fun n => (s (n + 1) - s n : ℝ)) =O[atTop] (fun n => (s n : ℝ)^ε) := by sorry

end Erdos208

theorem Erdos208.erdos_208.parts.i.disproof : ¬ (type_of% @Erdos208.erdos_208.parts.i) := sorry
