import FormalConjectures.Util.ProblemImports
open Nat Finset

theorem inv_eq_pow (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p) (x : ZMod p) :
    x⁻¹ = x ^ (p - 2) := by
  rcases eq_or_ne x 0 with h | h
  · subst h; rw [inv_zero, zero_pow (by omega)]
  · have hx : x ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h
    have hmul : x * x ^ (p - 2) = 1 := by
      rw [← _root_.pow_succ', show p - 2 + 1 = p - 1 by omega]; exact hx
    exact inv_eq_of_mul_eq_one_right hmul

theorem sum_inv_univ_eq_zero (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ x : ZMod p, x⁻¹ = 0 := by
  have h : ∀ x : ZMod p, x⁻¹ = x ^ (p - 2) := inv_eq_pow p (by omega)
  simp_rw [h]
  apply FiniteField.sum_pow_lt_card_sub_one
  rw [ZMod.card]; omega

theorem sum_inv_range_eq_zero (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ k ∈ Finset.Ico 1 p, ((k : ZMod p))⁻¹ = 0 := by
  haveI : NeZero p := ⟨by omega⟩
  have hbridge : (∑ x : ZMod p, x⁻¹) = ∑ k ∈ Finset.range p, ((k : ZMod p))⁻¹ := by
    apply Finset.sum_bij' (fun (x : ZMod p) _ => x.val) (fun (k : ℕ) _ => (k : ZMod p))
    · intro x _; simp [Finset.mem_range, ZMod.val_lt]
    · intro k hk; exact Finset.mem_univ _
    · intro x _; exact ZMod.natCast_zmod_val x
    · intro k hk; exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hk)
    · intro x _; rw [ZMod.natCast_zmod_val]
  rw [← sum_inv_univ_eq_zero p hp5, hbridge, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) (by omega : 1 ≤ p)]
  simp
