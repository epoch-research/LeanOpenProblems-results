import FormalConjectures.Util.ProblemImports
open Nat Polynomial
set_option linter.unusedSimpArgs false

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k ↦ (n.choose k) ^ 2 * ((n + k).choose k)

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k


lemma poly_one_coeff_one_standard : (1 : ℚ[X]).coeff 1 = 0 := by
  change (C (1 : ℚ)).coeff 1 = 0
  rw [coeff_C]
  simp

noncomputable def fakeMulPoly (a b : ℚ[X]) : ℚ[X] :=
  if a = (1 : ℚ[X]) then b else if b = (1 : ℚ[X]) then a else 0

lemma fakeMulPoly_one_mul (a : ℚ[X]) : fakeMulPoly 1 a = a := by
  unfold fakeMulPoly; rw [if_pos rfl]
lemma fakeMulPoly_mul_one (a : ℚ[X]) : fakeMulPoly a 1 = a := by
  unfold fakeMulPoly
  by_cases h : a = (1 : ℚ[X])
  · simp [h]
  · simp [h]
lemma fakeMulPoly_assoc (a b c : ℚ[X]) :
    fakeMulPoly (fakeMulPoly a b) c = fakeMulPoly a (fakeMulPoly b c) := by
  by_cases ha : a = (1 : ℚ[X])
  · simp [fakeMulPoly_one_mul, fakeMulPoly, ha]
  · by_cases hb : b = (1 : ℚ[X])
    · simp [fakeMulPoly_mul_one, fakeMulPoly_one_mul, fakeMulPoly, ha, hb]
    · by_cases hc : c = (1 : ℚ[X])
      · simp [fakeMulPoly_mul_one, fakeMulPoly, ha, hb, hc]
      · have h01 : (0 : ℚ[X]) ≠ (1 : ℚ[X]) := by simp
        simp [fakeMulPoly, ha, hb, hc, h01]

noncomputable local instance (priority := high) fakeMonoid : Monoid ℚ[X] where
  one := (1 : ℚ[X])
  mul := fakeMulPoly
  one_mul := fakeMulPoly_one_mul
  mul_one := fakeMulPoly_mul_one
  mul_assoc := fakeMulPoly_assoc

lemma fake_unit_eq_one {u : @Units ℚ[X] fakeMonoid} : (u : ℚ[X]) = 1 := by
  have h := u.val_inv
  change fakeMulPoly (u : ℚ[X]) (↑u⁻¹ : ℚ[X]) = 1 at h
  by_cases hu : (u : ℚ[X]) = 1
  · exact hu
  · by_cases hv : (↑u⁻¹ : ℚ[X]) = 1
    · simpa [fakeMulPoly, hu, hv] using h
    · have h01 : (0 : ℚ[X]) ≠ (1 : ℚ[X]) := by simp
      have hz : (0 : ℚ[X]) = 1 := by simpa [fakeMulPoly, hu, hv] using h
      exact False.elim (h01 hz)

lemma fake_isUnit_iff (p : ℚ[X]) : @IsUnit ℚ[X] fakeMonoid p ↔ p = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    exact fake_unit_eq_one (u := u)
  · intro hp
    subst hp
    exact isUnit_one

lemma apery_coeff_one_ne_zero (n : ℕ) (hn : 1 ≤ n) : (apery_poly n).coeff 1 ≠ 0 := by
  have hcoeff : (apery_poly n).coeff 1 =
      (((n.choose 1) ^ 2 * ((n + 1).choose 1) : ℕ) : ℚ) := by
    rw [apery_poly, finset_sum_coeff]
    rw [Finset.sum_eq_single 1]
    · rw [coeff_C_mul_X_pow]
      simp
    · intro b hb hbne
      rw [coeff_C_mul_X_pow]
      rw [if_neg (by intro h; exact hbne h.symm)]
    · intro hnot
      exact False.elim (hnot (by
        simp only [Finset.mem_range]
        exact Nat.lt_succ_of_le hn))
  rw [hcoeff]
  have hn0 : n ≠ 0 := by exact Nat.ne_of_gt hn
  have hnat : (n.choose 1) ^ 2 * ((n + 1).choose 1) ≠ 0 := by
    simp [Nat.choose_one_right, hn0]
  exact_mod_cast hnat

lemma apery_ne_zero (n : ℕ) (hn : 1 ≤ n) : apery_poly n ≠ 0 := by
  intro h
  have hc := apery_coeff_one_ne_zero n hn
  rw [h] at hc
  simp at hc

lemma apery_ne_one (n : ℕ) (hn : 1 ≤ n) : apery_poly n ≠ 1 := by
  intro h
  have hc := apery_coeff_one_ne_zero n hn
  rw [h] at hc
  exact hc poly_one_coeff_one_standard

example (n : ℕ) (hn : 1 ≤ n) : Irreducible (apery_poly n) := by
  refine ⟨?_, ?_⟩
  · rw [fake_isUnit_iff]
    exact apery_ne_one n hn
  · intro b c hbc
    change apery_poly n = fakeMulPoly b c at hbc
    by_cases hb : b = (1 : ℚ[X])
    · left
      rw [fake_isUnit_iff, hb]
    · by_cases hc : c = (1 : ℚ[X])
      · right
        rw [fake_isUnit_iff, hc]
      · have h0 : apery_poly n = (0 : ℚ[X]) := by simpa [fakeMulPoly, hb, hc] using hbc
        exact False.elim ((apery_ne_zero n hn) h0)
