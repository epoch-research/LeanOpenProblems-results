import FormalConjecturesUtil

/-! An obstruction to strengthening the conjecture to a simple restriction
on ratios of arbitrary ternary-good integers. This is not a counterexample
to Erdős 406. -/

namespace Erdos406PairRatio

lemma five_step_good_pair :
    Nat.digits 3 4961182 ⊆ [0, 1] ∧
    Nat.digits 3 5080250368 ⊆ [0, 1] ∧
    (5080250368 : ℕ) = 4 ^ 5 * 4961182 := by
  norm_num [Nat.digits_of_two_le_of_pos]

lemma five_step_multiplier_bad : ¬ Nat.digits 3 (4 ^ 5) ⊆ [0, 1] := by
  norm_num [Nat.digits_of_two_le_of_pos]

/-- Goodness of two endpoints with a power-of-four ratio does not imply
goodness of the multiplier. In particular, the endpoints cannot be replaced
by arbitrary good integers in an attempted classification argument. -/
theorem ratio_goodness_implication_false :
    ¬ (∀ n k : ℕ, 0 < n → Nat.digits 3 n ⊆ [0, 1] →
      Nat.digits 3 (4 ^ k * n) ⊆ [0, 1] → Nat.digits 3 (4 ^ k) ⊆ [0, 1]) := by
  intro h
  obtain ⟨h1, h2, he⟩ := five_step_good_pair
  rw [he] at h2
  exact five_step_multiplier_bad (h 4961182 5 (by decide) h1 h2)

#print axioms ratio_goodness_implication_false
end Erdos406PairRatio
