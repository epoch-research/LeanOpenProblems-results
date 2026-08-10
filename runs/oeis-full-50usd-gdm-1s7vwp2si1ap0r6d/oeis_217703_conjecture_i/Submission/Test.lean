import FormalConjectures.Util.ProblemImports

open Polynomial

noncomputable def Sn (n : ℕ) : Polynomial ℤ :=
  match n with
  | 0 => 1
  | 1 => X
  | k + 2 =>
    let m : ℕ := k + 1
    let Sm : Polynomial ℤ := Sn m
    let S_m_minus_1 : Polynomial ℤ := Sn k
    let m_int : ℤ := m
    let coeff_int : ℤ := 2 * m_int * (m_int + 1)
    let coeff_poly : Polynomial ℤ := Polynomial.X + Polynomial.C coeff_int
    coeff_poly * Sm - Polynomial.C (m_int ^ 4) * S_m_minus_1

lemma Sn_natDegree (n : ℕ) : (Sn n).natDegree = n := sorry -- we have this in Spec.lean

lemma Sn_four_eq : Sn 4 = X^4 + C 40 * X^3 + C 334 * X^2 + C 408 * X - C 207 := by
  have h4 : Sn 4 = (X + C (2 * 3 * 4)) * Sn 3 - C (3^4) * Sn 2 := rfl
  have h3 : Sn 3 = (X + C (2 * 2 * 3)) * Sn 2 - C (2^4) * Sn 1 := rfl
  have h2 : Sn 2 = (X + C (2 * 1 * 2)) * Sn 1 - C (1^4) * Sn 0 := rfl
  rw [h4, h3, h2, Sn_one, Sn_zero]
  ring

lemma Sn_four_map_eq :
  (Sn 4).map (Int.castRingHom (ZMod 7)) = X^4 + C 5 * X^3 + C 5 * X^2 + C 2 * X + C 3 := by
  ext i
  by_cases h : i ≤ 4
  · interval_cases i
    · -- i = 0
      rw [Sn_four_eq]
      simp
      decide
    · -- i = 1
      rw [Sn_four_eq]
      simp
      decide
    · -- i = 2
      rw [Sn_four_eq]
      simp
      decide
    · -- i = 3
      rw [Sn_four_eq]
      simp
      decide
    · -- i = 4
      rw [Sn_four_eq]
      simp
      decide
  · -- i > 4
    have h_lt : 4 < i := by omega
    have h1 : coeff ((Sn 4).map (Int.castRingHom (ZMod 7))) i = 0 := by
      rw [coeff_map]
      have : (Sn 4).natDegree = 4 := Sn_natDegree 4
      have : coeff (Sn 4) i = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      rw [this, map_zero]
    have h2 : coeff (X^4 + C 5 * X^3 + C 5 * X^2 + C 2 * X + C 3 : (ZMod 7)[X]) i = 0 := by
      -- we can prove this because the degree of the polynomial is 4
      apply coeff_eq_zero_of_natDegree_lt
      have : (X^4 + C 5 * X^3 + C 5 * X^2 + C 2 * X + C 3 : (ZMod 7)[X]).natDegree ≤ 4 := by
        decide
      omega
    rw [h1, h2]








