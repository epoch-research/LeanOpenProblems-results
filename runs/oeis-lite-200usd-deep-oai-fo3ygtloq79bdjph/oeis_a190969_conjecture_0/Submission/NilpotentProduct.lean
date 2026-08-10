import FormalConjectures.Util.ProblemImports

open Finset
open scoped BigOperators

lemma prod_one_sub_mul_square_zero {R : Type*} [CommRing R]
    (c : R) (f : ℕ → R) (hc : c ^ 2 = 0) (k : ℕ) :
    (∏ j ∈ Finset.range k, (1 - c * f j)) = 1 - c * (∑ j ∈ Finset.range k, f j) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.prod_range_succ, Finset.sum_range_succ, ih]
      calc
        (1 - c * (∑ x ∈ range k, f x)) * (1 - c * f k)
            = 1 - c * ((∑ x ∈ range k, f x) + f k) + (c ^ 2) * ((∑ x ∈ range k, f x) * f k) := by
              ring
        _ = 1 - c * ((∑ x ∈ range k, f x) + f k) := by
              rw [hc]
              simp


lemma zmod_natCast_pow_two_square_zero (p : ℕ) :
    ((((p : ℕ) : ZMod (p ^ 3)) ^ 2 : ZMod (p ^ 3)) ^ 2) = 0 := by
  rw [← pow_mul]
  change (((p : ℕ) : ZMod (p ^ 3)) ^ 4 : ZMod (p ^ 3)) = 0
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  exact pow_dvd_pow p (by norm_num : 3 ≤ 4)

lemma zmod_prod_one_sub_p2 (p k : ℕ) (f : ℕ → ZMod (p ^ 3)) :
    (∏ j ∈ Finset.range k, (1 - (((p : ℕ) : ZMod (p ^ 3)) ^ 2) * f j)) =
      1 - (((p : ℕ) : ZMod (p ^ 3)) ^ 2) * (∑ j ∈ Finset.range k, f j) := by
  exact prod_one_sub_mul_square_zero (((p : ℕ) : ZMod (p ^ 3)) ^ 2) f
    (zmod_natCast_pow_two_square_zero p) k


lemma odd_denom_coprime_p_pow {p j : ℕ} (hp : p.Prime) (hj : 2 * j + 1 < p) :
    Nat.Coprime (2 * j + 1) (p ^ 3) := by
  apply hp.coprime_pow_of_not_dvd
  intro hdiv
  have hpos : 0 < 2 * j + 1 := by omega
  have hge : p ≤ 2 * j + 1 := Nat.le_of_dvd hpos hdiv
  omega

lemma odd_denom_isUnit_zmod_p3 {p j : ℕ} (hp : p.Prime) (hj : 2 * j + 1 < p) :
    IsUnit (((2 * j + 1 : ℕ) : ZMod (p ^ 3))) := by
  rw [ZMod.isUnit_iff_coprime]
  exact odd_denom_coprime_p_pow hp hj


lemma zmod_prod_odd_harmonic_p3 (p k : ℕ) :
    (∏ j ∈ Finset.range k,
        (1 - (((p : ℕ) : ZMod (p ^ 3)) ^ 2) *
          ((((2 * j + 1 : ℕ) : ZMod (p ^ 3)) ^ 2)⁻¹))) =
      1 - (((p : ℕ) : ZMod (p ^ 3)) ^ 2) *
        (∑ j ∈ Finset.range k,
          ((((2 * j + 1 : ℕ) : ZMod (p ^ 3)) ^ 2)⁻¹)) := by
  exact zmod_prod_one_sub_p2 p k
    (fun j => ((((2 * j + 1 : ℕ) : ZMod (p ^ 3)) ^ 2)⁻¹))

lemma odd_denom_lt_of_mem_range {p k j : ℕ} (hkp : 2 * k < p) (hj : j ∈ Finset.range k) :
    2 * j + 1 < p := by
  have hjlt : j < k := Finset.mem_range.mp hj
  omega

lemma odd_denom_isUnit_zmod_p3_of_mem_range {p k j : ℕ}
    (hp : p.Prime) (hkp : 2 * k < p) (hj : j ∈ Finset.range k) :
    IsUnit (((2 * j + 1 : ℕ) : ZMod (p ^ 3))) := by
  exact odd_denom_isUnit_zmod_p3 hp (odd_denom_lt_of_mem_range hkp hj)


lemma zmod_natCast_pow_two_zero_mod_p2 (p : ℕ) :
    (((p : ℕ) : ZMod (p ^ 2)) ^ 2 : ZMod (p ^ 2)) = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]

lemma zmod_prod_odd_harmonic_p2 (p k : ℕ) :
    (∏ j ∈ Finset.range k,
        (1 - (((p : ℕ) : ZMod (p ^ 2)) ^ 2) *
          ((((2 * j + 1 : ℕ) : ZMod (p ^ 2)) ^ 2)⁻¹))) = 1 := by
  apply Finset.prod_eq_one
  intro j hj
  rw [zmod_natCast_pow_two_zero_mod_p2]
  simp


lemma odd_denom_coprime_p_pow2 {p j : ℕ} (hp : p.Prime) (hj : 2 * j + 1 < p) :
    Nat.Coprime (2 * j + 1) (p ^ 2) := by
  apply hp.coprime_pow_of_not_dvd
  intro hdiv
  have hpos : 0 < 2 * j + 1 := by omega
  have hge : p ≤ 2 * j + 1 := Nat.le_of_dvd hpos hdiv
  omega

lemma odd_denom_isUnit_zmod_p2_of_mem_range {p k j : ℕ}
    (hp : p.Prime) (hkp : 2 * k < p) (hj : j ∈ Finset.range k) :
    IsUnit (((2 * j + 1 : ℕ) : ZMod (p ^ 2))) := by
  rw [ZMod.isUnit_iff_coprime]
  exact odd_denom_coprime_p_pow2 hp (odd_denom_lt_of_mem_range hkp hj)
