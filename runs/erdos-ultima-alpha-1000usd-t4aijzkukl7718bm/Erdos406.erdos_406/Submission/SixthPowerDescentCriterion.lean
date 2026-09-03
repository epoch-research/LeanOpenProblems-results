import Submission.Work

/-! A conditional reduction to cube descent on squares. Neither descent
hypothesis is established here; this is not a settlement of Erdős 406. -/

namespace Erdos406SixthPowerCriterion
open Erdos406Work

lemma good_four_exponent_mod_three {m : ℕ}
    (hg : Nat.digits 3 (4 ^ m) ⊆ [0, 1]) : m % 3 = 0 ∨ m % 3 = 1 := by
  have hres : 4 ^ m % 9 = 4 ^ (m % 3) % 9 := by
    conv_lhs => rw [← Nat.mod_add_div m 3, pow_add, pow_mul]
    norm_num [Nat.mul_mod, Nat.pow_mod]
  have hd := ternary_digit_bound hg 1
  norm_num only [pow_one] at hd
  have hm : m % 3 < 3 := Nat.mod_lt _ (by decide)
  by_contra h
  have he : m % 3 = 2 := by omega
  rw [he] at hres
  norm_num at hres
  omega

/-- Both sixth-power descent premises would imply pure-power cubic descent.
The premises require whole-number digit conditions, not just finite windows. -/
theorem pure_power_descent_of_sixth
    (h6 : ∀ x : ℕ, Nat.digits 3 (x ^ 6) ⊆ [0, 1] →
      Nat.digits 3 (x ^ 2) ⊆ [0, 1])
    (h46 : ∀ x : ℕ, Nat.digits 3 (4 * x ^ 6) ⊆ [0, 1] →
      Nat.digits 3 (x ^ 2) ⊆ [0, 1]) :
    ∀ m : ℕ, Nat.digits 3 (4 ^ m) ⊆ [0, 1] →
      Nat.digits 3 (4 ^ (m / 3)) ⊆ [0, 1] := by
  intro m hg
  have hsq : (2 ^ (m / 3)) ^ 2 = 4 ^ (m / 3) := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    rfl
  have hsix : (2 ^ (m / 3)) ^ 6 = 4 ^ (3 * (m / 3)) := by
    rw [← pow_mul, show (m / 3) * 6 = 2 * (3 * (m / 3)) by omega, pow_mul]
    rfl
  rcases good_four_exponent_mod_three hg with hzero | hone
  · have he : m = 3 * (m / 3) := by omega
    have hh := h6 (2 ^ (m / 3)) (by simpa only [hsix, ← he] using hg)
    simpa only [hsq] using hh
  · have he : m = 3 * (m / 3) + 1 := by omega
    have hpow : 4 ^ m = 4 * (2 ^ (m / 3)) ^ 6 := by
      rw [hsix]
      conv_lhs => rw [he, pow_succ]
      exact Nat.mul_comm _ _
    have hh := h46 (2 ^ (m / 3)) (by simpa only [← hpow] using hg)
    simpa only [hsq] using hh

/-- Conditional finiteness, with the unproved global hypotheses explicit. -/
theorem finiteness_of_sixth_descent
    (h6 : ∀ x : ℕ, Nat.digits 3 (x ^ 6) ⊆ [0, 1] →
      Nat.digits 3 (x ^ 2) ⊆ [0, 1])
    (h46 : ∀ x : ℕ, Nat.digits 3 (4 * x ^ 6) ⊆ [0, 1] →
      Nat.digits 3 (x ^ 2) ⊆ [0, 1]) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  have hc := classification_iff_pure_power_descent.mpr
    (pure_power_descent_of_sixth h6 h46)
  apply Set.finite_iff_bddAbove.mpr
  refine ⟨256, ?_⟩
  rintro n ⟨⟨k, rfl⟩, hg⟩
  obtain ⟨m, hm⟩ := even_exponent hg
  have he : 2 ^ k = 4 ^ m := by
    rw [show k = 2 * m by omega, pow_mul]
    rfl
  rw [he] at hg ⊢
  rcases (hc m).mp hg with rfl | rfl | rfl <;> norm_num

#print axioms good_four_exponent_mod_three
#print axioms pure_power_descent_of_sixth
#print axioms finiteness_of_sixth_descent
end Erdos406SixthPowerCriterion
