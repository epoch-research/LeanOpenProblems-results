import FormalConjectures.Util.ProblemImports

open Finset

namespace Dev

/-- Sum of squares over `ZMod p` vanishes for `p ≥ 5` (a Wolstenholme ingredient). -/
lemma sum_sq_zero (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ x : ZMod p, x ^ 2 = 0 := by
  apply FiniteField.sum_pow_lt_card_sub_one
  rw [ZMod.card]
  omega

/-- Sum of first powers over `ZMod p` vanishes for `p ≥ 3`. -/
lemma sum_pow_one_zero (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p) :
    ∑ x : ZMod p, x ^ 1 = 0 := by
  apply FiniteField.sum_pow_lt_card_sub_one
  rw [ZMod.card]
  omega

/-- Sum of squared inverses over `ZMod p` vanishes for `p ≥ 5` (`H₂ ≡ 0 mod p`). -/
lemma sum_inv_sq_zero (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ x : ZMod p, (x⁻¹) ^ 2 = 0 := by
  have h : ∑ x : ZMod p, (x⁻¹) ^ 2 = ∑ y : ZMod p, y ^ 2 :=
    Fintype.sum_bijective (·⁻¹) inv_involutive.bijective
      (fun x => (x⁻¹) ^ 2) (fun y => y ^ 2) (fun x => rfl)
  rw [h]; exact sum_sq_zero p hp5

end Dev
