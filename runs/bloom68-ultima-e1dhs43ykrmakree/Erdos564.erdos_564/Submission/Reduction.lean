import FormalConjecturesUtil

/-! A reduction of the statement in Spec.lean, without assuming either theorem there. -/

open Combinatorics Real Filter

lemma tower_cast (k : ℕ) :
    (2 : ℝ) ^ ((2 : ℝ) ^ k) = ((2 ^ (2 ^ k) : ℕ) : ℝ) := by
  norm_cast

lemma exact_reduction :
    (∃ c > 0, ∀ᶠ n in atTop,
      (2 : ℝ) ^ (2 : ℝ) ^ (c * n) ≤ hypergraphRamsey 3 n) ↔
    ∀ᶠ n : ℕ in atTop, (2 : ℕ) ^ (2 ^ n) ≤ hypergraphRamsey 3 n := by
  constructor
  · rintro ⟨c, hc, h⟩
    filter_upwards [h] with n hn
    rw [tower_cast] at hn
    have hnat : (2 : ℕ) ^ (2 ^ (c * n)) ≤ hypergraphRamsey 3 n := by
      exact_mod_cast hn
    exact le_trans
      (Nat.pow_le_pow_right (by decide)
        (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_left n hc))) hnat
  · intro h
    refine ⟨1, by decide, ?_⟩
    filter_upwards [h] with n hn
    rw [one_mul, tower_cast]
    exact_mod_cast hn

lemma exact_negation :
    (¬ (∃ c > 0, ∀ᶠ n in atTop,
      (2 : ℝ) ^ (2 : ℝ) ^ (c * n) ≤ hypergraphRamsey 3 n)) ↔
    ∀ N : ℕ, ∃ n ≥ N, hypergraphRamsey 3 n < (2 : ℕ) ^ (2 ^ n) := by
  rw [exact_reduction, Filter.eventually_atTop]
  push_neg
  rfl

#print axioms exact_reduction
#print axioms exact_negation
