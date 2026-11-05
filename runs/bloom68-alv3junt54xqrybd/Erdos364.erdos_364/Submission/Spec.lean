import FormalConjecturesUtil

/-!
# Erdős Problem 364

*Reference:* [erdosproblems.com/364](https://www.erdosproblems.com/364)
-/

open Nat

namespace Erdos364

/-- There is no consecutive triple of powerful numbers. -/
theorem erdos_364 :
    ¬ ∃ (n : ℕ), Powerful n ∧ Powerful (n + 1) ∧ Powerful (n + 2) := by
  sorry

end Erdos364

theorem Erdos364.erdos_364.disproof : ¬ (type_of% @Erdos364.erdos_364) := sorry
