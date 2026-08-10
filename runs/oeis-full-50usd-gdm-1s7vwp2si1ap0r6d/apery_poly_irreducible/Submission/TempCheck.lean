import FormalConjectures.Util.ProblemImports

open Polynomial
open Nat

noncomputable def apery_poly_int (n : ℕ) : ℤ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℤ) * (X : ℤ[X]) ^ k

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

lemma apery_poly_map (n : ℕ) : map (Int.castRingHom ℚ) (apery_poly_int n) = apery_poly n := by
  dsimp [apery_poly, apery_poly_int]
  rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  simp

lemma apery_poly_int_coeff_zero (n : ℕ) : (apery_poly_int n).coeff 0 = 1 := by
  dsimp [apery_poly_int]
  rw [Polynomial.finset_sum_coeff]
  rw [Finset.sum_range_succ']
  simp






lemma IsPrimitive_of_coeff_zero_eq_one (g : ℤ[X]) (h : g.coeff 0 = 1) : g.IsPrimitive := by

  intro r hdvd
  have hd : r ∣ g.coeff 0 := by
    rcases hdvd with ⟨q, rfl⟩
    rw [coeff_C_mul]
    exact dvd_mul_right r (coeff q 0)
  rw [h] at hd
  exact isUnit_of_dvd_one hd

lemma irreducible_of_irreducible_map_to_zmod (f : ℤ[X]) (hprim : f.IsPrimitive) (p : ℕ) [hp : Fact p.Prime]

    (hlc : (f.leadingCoeff : ZMod p) ≠ 0)
    (h_irr : Irreducible (f.map (Int.castRingHom (ZMod p)))) :
    Irreducible f := by
  constructor
  · intro h_unit
    have h_map_unit := IsUnit.map (mapRingHom (Int.castRingHom (ZMod p))) h_unit
    exact h_irr.not_isUnit h_map_unit
  · intro a b hab
    have h_lc_mul : f.leadingCoeff = a.leadingCoeff * b.leadingCoeff := by
      rw [hab, leadingCoeff_mul]
    have h_lc_map : (f.leadingCoeff : ZMod p) = (a.leadingCoeff : ZMod p) * (b.leadingCoeff : ZMod p) := by
      rw [h_lc_mul]
      push_cast
      rfl
    have h_alc : (a.leadingCoeff : ZMod p) ≠ 0 := by
      intro hc
      apply hlc
      rw [h_lc_map, hc, zero_mul]
    have h_blc : (b.leadingCoeff : ZMod p) ≠ 0 := by
      intro hc
      apply hlc
      rw [h_lc_map, hc, mul_zero]
    have h_map : f.map (Int.castRingHom (ZMod p)) =
        a.map (Int.castRingHom (ZMod p)) * b.map (Int.castRingHom (ZMod p)) := by
      rw [hab, Polynomial.map_mul]
    rcases h_irr.isUnit_or_isUnit h_map with hu1 | hu2
    · left
      have h_deg1 : (a.map (Int.castRingHom (ZMod p))).natDegree = 0 := natDegree_eq_zero_of_isUnit hu1
      have h_deg2 : (a.map (Int.castRingHom (ZMod p))).natDegree = a.natDegree :=
        Polynomial.natDegree_map_of_leadingCoeff_ne_zero (Int.castRingHom (ZMod p)) h_alc
      have h_deg3 : a.natDegree = 0 := by
        rw [← h_deg2, h_deg1]
      have h_eq_C : a = C (coeff a 0) := eq_C_of_natDegree_eq_zero h_deg3
      have hdvd : C (coeff a 0) ∣ f := ⟨b, by rw [hab, ← h_eq_C]⟩
      have h_unit_coeff : IsUnit (coeff a 0) := hprim (coeff a 0) hdvd
      rw [h_eq_C]
      exact isUnit_C.mpr h_unit_coeff
    · right
      have h_deg1 : (b.map (Int.castRingHom (ZMod p))).natDegree = 0 := natDegree_eq_zero_of_isUnit hu2
      have h_deg2 : (b.map (Int.castRingHom (ZMod p))).natDegree = b.natDegree :=
        Polynomial.natDegree_map_of_leadingCoeff_ne_zero (Int.castRingHom (ZMod p)) h_blc
      have h_deg3 : b.natDegree = 0 := by
        rw [← h_deg2, h_deg1]
      have h_eq_C : b = C (coeff b 0) := eq_C_of_natDegree_eq_zero h_deg3
      have hdvd : C (coeff b 0) ∣ f := ⟨a, by rw [hab, mul_comm, ← h_eq_C]⟩
      have h_unit_coeff : IsUnit (coeff b 0) := hprim (coeff b 0) hdvd
      rw [h_eq_C]
      exact isUnit_C.mpr h_unit_coeff































