import FormalConjecturesUtil

/-!
# Erdős Problem 7

*Reference:* [erdosproblems.com/7](https://www.erdosproblems.com/7)
-/

namespace Erdos7

open Set

/--
Is there a covering system all of whose moduli are odd (and greater than 1)?
-/
theorem erdos_7 : 
    ∃ (C : StrictCoveringSystem ℤ), ∀ i,
      ¬ C.moduli i ≤ Ideal.span {2} ∧ C.moduli i ≠ ⊤ := by
  sorry

end Erdos7
