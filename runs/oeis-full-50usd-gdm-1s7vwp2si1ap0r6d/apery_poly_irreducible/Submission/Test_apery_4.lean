import FormalConjectures.Util.ProblemImports

open Nat
open Polynomial

noncomputable def apery_poly_int (n : ℕ) : ℤ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℤ) * (X : ℤ[X]) ^ k

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

lemma IsPrimitive_of_coeff_zero_eq_one (g : ℤ[X]) (h : g.coeff 0 = 1) : g.IsPrimitive := by
  intro r hdvd
  have hd : r ∣ g.coeff 0 := by
    rcases hdvd with ⟨q, rfl⟩
    rw [coeff_C_mul]
    exact dvd_mul_right r (coeff q 0)
  rw [h] at hd
  exact isUnit_of_dvd_one hd

lemma apery_poly_int_coeff_zero (n : ℕ) : (apery_poly_int n).coeff 0 = 1 := by
  dsimp [apery_poly_int]
  rw [Polynomial.finset_sum_coeff]
  rw [Finset.sum_range_succ']
  simp

lemma apery_poly_map (n : ℕ) : map (Int.castRingHom ℚ) (apery_poly_int n) = apery_poly n := by
  dsimp [apery_poly, apery_poly_int]
  rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  simp

lemma apery_poly_int_4 : apery_poly_int 4 = 70 * X ^ 4 + 560 * X ^ 3 + 540 * X ^ 2 + 80 * X + 1 := by
  dsimp [apery_poly_int]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  simp
  have h3 : ((choose 4 2 : ℕ) : ℤ[X]) = 6 := rfl
  have h4 : ((choose 6 2 : ℕ) : ℤ[X]) = 15 := rfl
  have h6 : ((choose 7 3 : ℕ) : ℤ[X]) = 35 := rfl
  have h8 : ((choose 8 4 : ℕ) : ℤ[X]) = 70 := rfl
  rw [h3, h4, h6, h8]
  ring

lemma apery_poly_int_4_natDegree : (apery_poly_int 4).natDegree = 4 := by
  rw [apery_poly_int_4]
  compute_degree!

lemma apery_poly_int_4_leadingCoeff : (apery_poly_int 4).leadingCoeff = 70 := by
  have : (apery_poly_int 4).leadingCoeff = coeff (apery_poly_int 4) 4 := by
    rw [leadingCoeff, apery_poly_int_4_natDegree]
  rw [this, apery_poly_int_4]
  simp [coeff_X, coeff_one]

lemma map_apery_poly_int_4 : map (Int.castRingHom (ZMod 5)) (apery_poly_int 4) = 1 := by
  rw [apery_poly_int_4]
  have h70 : (70 : ZMod 5) = 0 := rfl
  have h560 : (560 : ZMod 5) = 0 := rfl
  have h540 : (540 : ZMod 5) = 0 := rfl
  have h80 : (80 : ZMod 5) = 0 := rfl
  ext d
  simp [h70, h560, h540, h80]

lemma natDegree_lt_of_leadingCoeff_divisible {p : ℕ} [hp : Fact p.Prime] (g : ℤ[X]) (k : ℕ)
    (h_deg : natDegree (map (Int.castRingHom (ZMod p)) g) < k) (h_ge : k ≤ g.natDegree) :
    (p : ℤ) ∣ g.leadingCoeff := by
  have h_lt : natDegree (map (Int.castRingHom (ZMod p)) g) < g.natDegree := by linarith
  have h_coeff : coeff (map (Int.castRingHom (ZMod p)) g) g.natDegree = 0 := coeff_eq_zero_of_natDegree_lt h_lt
  rw [coeff_map] at h_coeff
  have h_coeff_cast : ((coeff g g.natDegree : ℤ) : ZMod p) = 0 := h_coeff
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_coeff_cast
  exact h_coeff_cast

lemma natDegree_map_lt_of_mul {p : ℕ} [hp : Fact p.Prime] (f g h : ℤ[X]) (k : ℕ)
    (h_mul : f = g * h) (h_f : natDegree (map (Int.castRingHom (ZMod p)) f) < k) (h_c0 : f.coeff 0 = 1) :
    natDegree (map (Int.castRingHom (ZMod p)) g) < k ∧ natDegree (map (Int.castRingHom (ZMod p)) h) < k := by
  have h_map_mul : map (Int.castRingHom (ZMod p)) f = map (Int.castRingHom (ZMod p)) g * map (Int.castRingHom (ZMod p)) h := by
    rw [h_mul, Polynomial.map_mul]
  have h_f_nz : map (Int.castRingHom (ZMod p)) f ≠ 0 := by
    intro hc
    have h_c : coeff (map (Int.castRingHom (ZMod p)) f) 0 = 0 := by rw [hc, coeff_zero]
    rw [coeff_map, h_c0] at h_c
    simp at h_c
  have h_g_nz : map (Int.castRingHom (ZMod p)) g ≠ 0 := by
    intro hc
    apply h_f_nz
    rw [h_map_mul, hc, zero_mul]
  have h_h_nz : map (Int.castRingHom (ZMod p)) h ≠ 0 := by
    intro hc
    apply h_f_nz
    rw [h_map_mul, hc, mul_zero]
  have h_deg_add : natDegree (map (Int.castRingHom (ZMod p)) f) =
      natDegree (map (Int.castRingHom (ZMod p)) g) + natDegree (map (Int.castRingHom (ZMod p)) h) := by
    rw [h_map_mul, natDegree_mul h_g_nz h_h_nz]
  rw [h_deg_add] at h_f
  exact ⟨by linarith, by linarith⟩

lemma proper_factor_degree_restriction {p : ℕ} [hp : Fact p.Prime] (f g h : ℤ[X]) (k : ℕ)
    (h_mul : f = g * h)
    (h_f : natDegree (map (Int.castRingHom (ZMod p)) f) < k)
    (h_c0 : f.coeff 0 = 1)
    (h_lc : ¬ (p : ℤ) ^ 2 ∣ f.leadingCoeff) :
    g.natDegree < k ∨ h.natDegree < k := by
  by_contra! h_deg
  have h_g_lt := (natDegree_map_lt_of_mul f g h k h_mul h_f h_c0).1
  have h_h_lt := (natDegree_map_lt_of_mul f g h k h_mul h_f h_c0).2
  have h_g_dvd := natDegree_lt_of_leadingCoeff_divisible g k h_g_lt h_deg.1
  have h_h_dvd := natDegree_lt_of_leadingCoeff_divisible h k h_h_lt h_deg.2
  have h_lc_eq : f.leadingCoeff = g.leadingCoeff * h.leadingCoeff := by
    rw [h_mul, leadingCoeff_mul (p := g) (q := h)]
  have h_p2_dvd : (p : ℤ) ^ 2 ∣ f.leadingCoeff := by
    rw [h_lc_eq]
    have : (p : ℤ) ^ 2 = (p : ℤ) * (p : ℤ) := by ring
    rw [this]
    exact mul_dvd_mul h_g_dvd h_h_dvd
  exact h_lc h_p2_dvd

theorem apery_poly_int_4_irreducible : Irreducible (apery_poly_int 4) := by
  constructor
  · intro h_unit
    rw [isUnit_iff] at h_unit
    rcases h_unit with ⟨r, hr, h_eq⟩
    have h_coeff : coeff (apery_poly_int 4) 4 = coeff (C r) 4 := by
      exact congrArg (coeff · 4) h_eq.symm
    rw [apery_poly_int_4] at h_coeff
    have hRHS : coeff (C r) 4 = 0 := by
      exact coeff_C
    rw [hRHS] at h_coeff
    simp [coeff_X, coeff_one] at h_coeff
  · intro g h h_mul
    have hp : Fact (Nat.Prime 5) := ⟨by decide⟩
    have h_deg : natDegree (map (Int.castRingHom (ZMod 5)) (apery_poly_int 4)) < 1 := by
      rw [map_apery_poly_int_4]
      simp
    have h_c0 : (apery_poly_int 4).coeff 0 = 1 := apery_poly_int_coeff_zero 4
    have h_lc : ¬ (5 : ℤ) ^ 2 ∣ (apery_poly_int 4).leadingCoeff := by
      rw [apery_poly_int_4_leadingCoeff]
      decide
    have h_rest := proper_factor_degree_restriction (apery_poly_int 4) g h 1 h_mul h_deg h_c0 h_lc
    rcases h_rest with hg | hh
    · left
      have hg0 : g.natDegree = 0 := by omega
      have h_eq : g = C (coeff g 0) := eq_C_of_natDegree_eq_zero hg0
      have hdvd : C (coeff g 0) ∣ apery_poly_int 4 := by
        rw [← h_eq]
        exact ⟨h, h_mul⟩
      have hprim : IsPrimitive (apery_poly_int 4) := IsPrimitive_of_coeff_zero_eq_one (apery_poly_int 4) h_c0
      have h_unit_coeff : IsUnit (coeff g 0) := hprim (coeff g 0) hdvd
      rw [h_eq]
      exact isUnit_C.mpr h_unit_coeff
    · right
      have hh0 : h.natDegree = 0 := by omega
      have h_eq : h = C (coeff h 0) := eq_C_of_natDegree_eq_zero hh0
      have hdvd : C (coeff h 0) ∣ apery_poly_int 4 := by
        rw [← h_eq]
        exact ⟨g, by rw [h_mul, mul_comm]⟩
      have hprim : IsPrimitive (apery_poly_int 4) := IsPrimitive_of_coeff_zero_eq_one (apery_poly_int 4) h_c0
      have h_unit_coeff : IsUnit (coeff h 0) := hprim (coeff h 0) hdvd
      rw [h_eq]
      exact isUnit_C.mpr h_unit_coeff

theorem apery_poly_4_irreducible : Irreducible (apery_poly 4) := by
  have hprim : IsPrimitive (apery_poly_int 4) := IsPrimitive_of_coeff_zero_eq_one (apery_poly_int 4) (apery_poly_int_coeff_zero 4)
  rw [← apery_poly_map 4]
  rw [← Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim]
  exact apery_poly_int_4_irreducible
