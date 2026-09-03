import FormalConjecturesUtil

/-!
An obstruction to a naive finite-gap extension construction for Erdős 972.
This is neither a proof nor a disproof of the conjecture.
-/

namespace IntervalExtension972

def primeSet (α : ℝ) : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ Nat.Prime ⌊(α * p)⌋₊}

lemma finite_gap_then_forced_success {α : ℝ}
    (hlo : (18 : ℝ) / 13 ≤ α) (hhi : α < (7 : ℝ) / 5) :
    (∀ p : ℕ, 2 < p → p ≤ 13 → p ∉ primeSet α) ∧ 17 ∈ primeSet α := by
  have hfloor (p q : ℕ) (h₁ : (q : ℝ) ≤ α * p)
      (h₂ : α * p < (q : ℝ) + 1) : ⌊(α * p)⌋₊ = q :=
    (Nat.floor_eq_iff ((Nat.cast_nonneg q).trans h₁)).mpr ⟨h₁, h₂⟩
  have h3 : ⌊(α * 3)⌋₊ = 4 := hfloor 3 4 (by norm_num; linarith) (by norm_num; linarith)
  have h5 : ⌊(α * 5)⌋₊ = 6 := hfloor 5 6 (by norm_num; linarith) (by norm_num; linarith)
  have h7 : ⌊(α * 7)⌋₊ = 9 := hfloor 7 9 (by norm_num; linarith) (by norm_num; linarith)
  have h11 : ⌊(α * 11)⌋₊ = 15 := hfloor 11 15 (by norm_num; linarith) (by norm_num; linarith)
  have h13 : ⌊(α * 13)⌋₊ = 18 := hfloor 13 18 (by norm_num; linarith) (by norm_num; linarith)
  have h17 : ⌊(α * 17)⌋₊ = 23 := hfloor 17 23 (by norm_num; linarith) (by norm_num; linarith)
  constructor
  · intro p hp2 hp13 hp
    rcases hp with ⟨hp, hq⟩
    interval_cases p <;> norm_num at hp <;> norm_num [h3, h5, h7, h11, h13] at hq
  · norm_num [primeSet, h17]

#print axioms finite_gap_then_forced_success

end IntervalExtension972
