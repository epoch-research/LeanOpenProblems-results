import Submission.LambertDifferenceOperators

/-! An obstruction to exact row annihilation in a short sampling window.
This is auxiliary work, not a settlement of Erdős 68. -/

namespace SingleJumpAnnihilation

open Finset LambertDifferenceOperators

/-- Two different two-level rows with the same partition cannot both be
annihilated without annihilating the constant row. Rational weights are
allowed here; no integer-weight or boundary-integrality assumption is used. -/
theorem two_level_annihilation {ι : Type*} (s : Finset ι)
    (z : ι → ℚ) (p : ι → Prop) [DecidablePred p]
    (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (h₁ : ∑ i ∈ s, z i * (if p i then 1 / a else 1) = 0)
    (h₂ : ∑ i ∈ s, z i * (if p i then 1 / b else 1) = 0) :
    ∑ i ∈ s, z i = 0 := by
  let L : ℚ := ∑ i ∈ s, if p i then 0 else z i
  let R : ℚ := ∑ i ∈ s, if p i then z i else 0
  have heq (x : ℚ) :
      (∑ i ∈ s, z i * (if p i then 1 / x else 1)) = L + R / x := by
    dsimp [L, R]
    rw [Finset.sum_div, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp [div_eq_mul_inv]
  have hL : (∑ i ∈ s, z i) = L + R := by
    dsimp [L, R]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp
  rw [heq] at h₁ h₂
  have h₁' : a * L + R = 0 := by
    have h := congrArg (fun x : ℚ => a * x) h₁
    field_simp at h
    nlinarith
  have h₂' : b * L + R = 0 := by
    have h := congrArg (fun x : ℚ => b * x) h₂
    field_simp at h
    nlinarith
  have hz : (a - b) * L = 0 := by nlinarith
  have hl : L = 0 := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hab)
  have hr : R = 0 := by simpa [hl] using h₁'
  simp [hL, hl, hr]

/-- A geometric row whose exponents have two adjacent values is a nonzero
constant multiple of its corresponding two-level row. -/
lemma inverse_power_two_levels (a : ℚ) (k : ℕ)
    (p : Prop) [Decidable p] :
    1 / a ^ (k + if p then 1 else 0) =
      (1 / a ^ k) * (if p then 1 / a else 1) := by
  split_ifs <;> simp [pow_succ, div_eq_mul_inv, mul_comm]

/-- Distinct geometric bases and the same single-jump partition force zero
constant coefficient, even when the two initial exponents differ. -/
theorem geometric_single_jump {ι : Type*} (s : Finset ι)
    (z : ι → ℚ) (p : ι → Prop) [DecidablePred p]
    (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (k l : ℕ)
    (h₁ : ∑ i ∈ s, z i / a ^ (k + if p i then 1 else 0) = 0)
    (h₂ : ∑ i ∈ s, z i / b ^ (l + if p i then 1 else 0) = 0) :
    ∑ i ∈ s, z i = 0 := by
  apply two_level_annihilation s z p a b ha hb hab
  · have he : (∑ i ∈ s, z i / a ^ (k + if p i then 1 else 0)) =
        (1 / a ^ k) * (∑ i ∈ s, z i * (if p i then 1 / a else 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [div_eq_mul_one_div, inverse_power_two_levels a]
      ring
    rw [he] at h₁
    exact (mul_eq_zero.mp h₁).resolve_left (one_div_ne_zero (pow_ne_zero _ ha))
  · have he : (∑ i ∈ s, z i / b ^ (l + if p i then 1 else 0)) =
        (1 / b ^ l) * (∑ i ∈ s, z i * (if p i then 1 / b else 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [div_eq_mul_one_div, inverse_power_two_levels b]
      ring
    rw [he] at h₂
    exact (mul_eq_zero.mp h₂).resolve_left (one_div_ne_zero (pow_ne_zero _ hb))


lemma div_two_mul (u n : ℕ) (hn : 4 * u ≤ n) (hn' : n < 8 * u) :
    n / (2 * u) = 2 + if 6 * u ≤ n then 1 else 0 := by
  split_ifs with h
  · norm_num
    apply Nat.div_eq_of_lt_le <;> omega
  · norm_num
    apply Nat.div_eq_of_lt_le <;> omega

lemma div_three_mul (u n : ℕ) (hn : 4 * u ≤ n) (hn' : n < 8 * u) :
    n / (3 * u) = 1 + if 6 * u ≤ n then 1 else 0 := by
  split_ifs with h
  · norm_num
    apply Nat.div_eq_of_lt_le <;> omega
  · norm_num
    apply Nat.div_eq_of_lt_le <;> omega

/-- On the interval [4u,8u), rows 2u and 3u have the same unique jump at
6u. Annihilating both therefore forces the constant coefficient to vanish.
The weights may be rational and the sample indices need not be consecutive. -/
theorem factorial_window {ι : Type*} (s : Finset ι) (z : ι → ℚ)
    (n : ι → ℕ) (u : ℕ) (hu : 0 < u)
    (hn : ∀ i ∈ s, 4 * u ≤ n i ∧ n i < 8 * u)
    (h₁ : ∑ i ∈ s, z i / ((2 * u).factorial : ℚ) ^ (n i / (2 * u)) = 0)
    (h₂ : ∑ i ∈ s, z i / ((3 * u).factorial : ℚ) ^ (n i / (3 * u)) = 0) :
    ∑ i ∈ s, z i = 0 := by
  have ha : ((2 * u).factorial : ℚ) ≠ 0 := by positivity
  have hb : ((3 * u).factorial : ℚ) ≠ 0 := by positivity
  have hab : ((2 * u).factorial : ℚ) ≠ (3 * u).factorial := by
    apply ne_of_lt
    exact_mod_cast (Nat.factorial_lt (show 0 < 2 * u by omega)).mpr
      (show 2 * u < 3 * u by omega)
  apply geometric_single_jump s z (fun i => 6 * u ≤ n i)
    ((2 * u).factorial : ℚ) ((3 * u).factorial : ℚ) ha hb hab 2 1
  · convert h₁ using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [div_two_mul u (n i) (hn i hi).1 (hn i hi).2]
  · convert h₂ using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [div_three_mul u (n i) (hn i hi).1 (hn i hi).2]


/-- The same obstruction with the full geometric row denominator included. -/
theorem factorial_window_rows {ι : Type*} (s : Finset ι) (z : ι → ℚ)
    (n : ι → ℕ) (u : ℕ) (hu : 0 < u)
    (hn : ∀ i ∈ s, 4 * u ≤ n i ∧ n i < 8 * u)
    (h₁ : ∑ i ∈ s, z i /
      (((2 * u).factorial : ℚ) ^ (n i / (2 * u)) * ((2 * u).factorial - 1)) = 0)
    (h₂ : ∑ i ∈ s, z i /
      (((3 * u).factorial : ℚ) ^ (n i / (3 * u)) * ((3 * u).factorial - 1)) = 0) :
    ∑ i ∈ s, z i = 0 := by
  have ha : (1 : ℚ) < (2 * u).factorial := by
    exact_mod_cast (Nat.one_lt_factorial.mpr (show 1 < 2 * u by omega))
  have hb : (1 : ℚ) < (3 * u).factorial := by
    exact_mod_cast (Nat.one_lt_factorial.mpr (show 1 < 3 * u by omega))
  simp_rw [← div_div] at h₁ h₂
  rw [← Finset.sum_div] at h₁ h₂
  apply factorial_window s z n u hu hn
  · exact (div_eq_zero_iff.mp h₁).resolve_right (by linarith)
  · exact (div_eq_zero_iff.mp h₂).resolve_right (by linarith)

end SingleJumpAnnihilation

#print axioms SingleJumpAnnihilation.two_level_annihilation
#print axioms SingleJumpAnnihilation.geometric_single_jump

#print axioms SingleJumpAnnihilation.factorial_window

#print axioms SingleJumpAnnihilation.factorial_window_rows
