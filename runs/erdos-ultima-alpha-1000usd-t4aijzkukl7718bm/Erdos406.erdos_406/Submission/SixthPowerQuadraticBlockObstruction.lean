import Submission.CubicBlockRigidity

/-! A coefficientwise obstruction for sixth powers of quadratic polynomials.
It applies to separated-block constructions, not to arbitrary integers with
ternary digits that may interact by carries. It does not settle Erdős 406. -/

namespace Erdos406SixthQuadratic
open Polynomial Erdos406Work

private def Good9 (n : ℕ) : Prop :=
  n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 3 ∨ n % 9 = 4

private lemma good9_of_good {n : ℕ} (h : Nat.digits 3 n ⊆ [0, 1]) : Good9 n := by
  have h0 := ternary_digit_bound h 0
  have h1 := ternary_digit_bound h 1
  norm_num only [pow_zero, pow_one, Nat.div_one] at h0 h1
  dsimp [Good9]
  omega

private lemma modular_certificate : ∀ a b c : Fin 9,
    (a : ℕ) % 3 ≠ 0 → (c : ℕ) % 3 ≠ 0 →
    ¬ (Good9 (6 * (a : ℕ)^5 * (b : ℕ)) ∧
      Good9 (15 * (a : ℕ)^4 * (b : ℕ)^2 + 6 * (a : ℕ)^5 * (c : ℕ)) ∧
      Good9 ((b : ℕ)^6 + 30*(a : ℕ)*(b : ℕ)^4*(c : ℕ) +
        90*(a : ℕ)^2*(b : ℕ)^2*(c : ℕ)^2 + 20*(a : ℕ)^3*(c : ℕ)^3) ∧
      Good9 (6 * (b : ℕ) * (c : ℕ)^5)) := by
  simp only [Good9]
  decide +kernel

/-- Among four coefficients of the sixth power of a quadratic whose endpoint
coefficients are units modulo three, at least one has a bad ternary digit. -/
theorem four_coefficients_not_all_good (a b c : ℕ)
    (ha : a % 3 ≠ 0) (hc : c % 3 ≠ 0) :
    ¬ (Nat.digits 3 (6*a^5*b) ⊆ [0, 1] ∧
      Nat.digits 3 (15*a^4*b^2 + 6*a^5*c) ⊆ [0, 1] ∧
      Nat.digits 3 (b^6 + 30*a*b^4*c + 90*a^2*b^2*c^2 + 20*a^3*c^3) ⊆ [0, 1] ∧
      Nat.digits 3 (6*b*c^5) ⊆ [0, 1]) := by
  rintro ⟨h1, h2, h6, h11⟩
  have h1' := good9_of_good h1
  have h2' := good9_of_good h2
  have h6' := good9_of_good h6
  have h11' := good9_of_good h11
  have hd : 3 ∣ 9 := by decide
  have h := modular_certificate ⟨a % 9, Nat.mod_lt _ (by decide)⟩
    ⟨b % 9, Nat.mod_lt _ (by decide)⟩ ⟨c % 9, Nat.mod_lt _ (by decide)⟩
    (by simpa only [Nat.mod_mod_of_dvd _ hd] using ha)
    (by simpa only [Nat.mod_mod_of_dvd _ hd] using hc)
  apply h
  simpa only [Good9, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod] using
    And.intro h1' (And.intro h2' (And.intro h6' h11'))

lemma quadratic_sixth_coefficients (a b c : ℕ) :
    let P : ℕ[X] := C a + C b * X + C c * X^2
    (P^6).coeff 1 = 6*a^5*b ∧
    (P^6).coeff 2 = 15*a^4*b^2 + 6*a^5*c ∧
    (P^6).coeff 6 = b^6 + 30*a*b^4*c + 90*a^2*b^2*c^2 + 20*a^3*c^3 ∧
    (P^6).coeff 11 = 6*b*c^5 := by
  dsimp only
  have he : (C a + C b * X + C c * X^2 : ℕ[X])^6 =
      C (a^6) +
      C (6*a^5*b) * X +
      C (6*a^5*c + 15*a^4*b^2) * X^2 +
      C (30*a^4*b*c + 20*a^3*b^3) * X^3 +
      C (15*a^4*c^2 + 60*a^3*b^2*c + 15*a^2*b^4) * X^4 +
      C (60*a^3*b*c^2 + 60*a^2*b^3*c + 6*a*b^5) * X^5 +
      C (20*a^3*c^3 + 90*a^2*b^2*c^2 + 30*a*b^4*c + b^6) * X^6 +
      C (60*a^2*b*c^3 + 60*a*b^3*c^2 + 6*b^5*c) * X^7 +
      C (15*a^2*c^4 + 60*a*b^2*c^3 + 15*b^4*c^2) * X^8 +
      C (30*a*b*c^4 + 20*b^3*c^3) * X^9 +
      C (6*a*c^5 + 15*b^2*c^4) * X^10 +
      C (6*b*c^5) * X^11 +
      C (c^6) * X^12 := by
    simp only [map_add, map_mul, map_pow, map_ofNat]
    ring
  rw [he]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  norm_num
  ring_nf
  trivial

/-- This is about the individual polynomial coefficients, before evaluation.
One cannot drop this distinction: evaluation at three can introduce carries. -/
theorem quadratic_sixth_not_coefficientwise_good (a b c : ℕ)
    (ha : a % 3 ≠ 0) (hc : c % 3 ≠ 0) :
    ¬ (∀ j : ℕ, Nat.digits 3
      (((C a + C b * X + C c * X^2 : ℕ[X])^6).coeff j) ⊆ [0, 1]) := by
  intro h
  obtain ⟨h1,h2,h6,h11⟩ := quadratic_sixth_coefficients a b c
  apply four_coefficients_not_all_good a b c ha hc
  exact ⟨h1 ▸ h 1, h2 ▸ h 2, h6 ▸ h 6, h11 ▸ h 11⟩

/-- The thirteen coefficients, in increasing degree order. -/
def sixthCoefficients (a b c : ℕ) : List ℕ :=
  [a^6,
    6*a^5*b,
    15*a^4*b^2 + 6*a^5*c,
    30*a^4*b*c + 20*a^3*b^3,
    15*a^4*c^2 + 60*a^3*b^2*c + 15*a^2*b^4,
    60*a^3*b*c^2 + 60*a^2*b^3*c + 6*a*b^5,
    b^6 + 30*a*b^4*c + 90*a^2*b^2*c^2 + 20*a^3*c^3,
    60*a^2*b*c^3 + 60*a*b^3*c^2 + 6*b^5*c,
    15*a^2*c^4 + 60*a*b^2*c^3 + 15*b^4*c^2,
    30*a*b*c^4 + 20*b^3*c^3,
    6*a*c^5 + 15*b^2*c^4,
    6*b*c^5,
    c^6]

lemma ofDigits_sixthCoefficients (a b c q : ℕ) :
    Nat.ofDigits q (sixthCoefficients a b c) = (a+b*q+c*q^2)^6 := by
  simp only [sixthCoefficients, Nat.ofDigits_cons, Nat.ofDigits_nil]
  ring

lemma good_ofDigits_blocks_iff (w : List ℕ) (L : ℕ)
    (hw : ∀ d ∈ w, d < 3^L) :
    Nat.digits 3 (Nat.ofDigits (3^L) w) ⊆ [0, 1] ↔
      ∀ d ∈ w, Nat.digits 3 d ⊆ [0, 1] := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [Nat.ofDigits_cons, good_split_iff (hw a (by simp))]
    rw [ih (fun d hd => hw d (by simp [hd]))]
    simp

/-- A uniform exclusion in the block spacing L. The size hypothesis is
essential: it prevents every carry between successive coefficient blocks. -/
theorem separated_quadratic_sixth_bad (a b c L : ℕ)
    (ha : a % 3 ≠ 0) (hc : c % 3 ≠ 0)
    (hsize : (a+b+c)^6 < 3^L) :
    ¬ Nat.digits 3 ((a+b*3^L+c*(3^L)^2)^6) ⊆ [0, 1] := by
  intro hg
  have hsum : (sixthCoefficients a b c).sum = (a+b+c)^6 := by
    simpa only [Nat.ofDigits_one, one_pow, mul_one] using ofDigits_sixthCoefficients a b c 1
  have hbound : ∀ d ∈ sixthCoefficients a b c, d < 3^L := by
    intro d hd
    have hle : d ≤ (sixthCoefficients a b c).sum := List.le_sum_of_mem hd
    rw [hsum] at hle
    omega
  rw [← ofDigits_sixthCoefficients a b c (3^L)] at hg
  have hall := (good_ofDigits_blocks_iff _ L hbound).mp hg
  apply four_coefficients_not_all_good a b c ha hc
  exact ⟨hall _ (by simp [sixthCoefficients]),
    hall _ (by simp [sixthCoefficients]),
    hall _ (by simp [sixthCoefficients]),
    hall _ (by simp [sixthCoefficients])⟩

#print axioms separated_quadratic_sixth_bad

#print axioms four_coefficients_not_all_good
#print axioms quadratic_sixth_not_coefficientwise_good
end Erdos406SixthQuadratic
