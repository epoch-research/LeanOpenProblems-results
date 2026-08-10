import FormalConjectures.Util.ProblemImports

open Nat
open Polynomial

def apery_coeff (n k : ℕ) : ℕ := (n.choose k) ^ 2 * ((n + k).choose k)

lemma apery_coeff_dvd (n k p : ℕ) (hp : p.Prime) (hn : n < p) (h : p ≤ n + k) (hk : k ≤ n) :
    p ∣ apery_coeff n k := by
  dsimp [apery_coeff]
  have hk_lt : k < p := by linarith
  have hn_lt : n < p := hn
  have hdvd : p ∣ (n + k).choose k := by
    have h_eq : k + n = n + k := Nat.add_comm k n
    have hd : p ∣ (k + n).choose k := Nat.Prime.dvd_choose_add hp hk_lt hn_lt (by linarith)
    rwa [h_eq] at hd
  exact dvd_mul_of_dvd_right hdvd _

noncomputable def apery_poly_int (n : ℕ) : ℤ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℤ) * (X : ℤ[X]) ^ k

lemma apery_poly_int_coeff_zero (n : ℕ) : (apery_poly_int n).coeff 0 = 1 := by
  dsimp [apery_poly_int]
  rw [Polynomial.finset_sum_coeff]
  rw [Finset.sum_range_succ']
  simp

lemma apery_poly_int_coeff (n k : ℕ) :
    (apery_poly_int n).coeff k = if k ≤ n then (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℤ) else 0 := by
  dsimp [apery_poly_int]
  rw [Polynomial.finset_sum_coeff]
  split_ifs with h
  · rw [Finset.sum_eq_single k]
    · rw [coeff_C_mul_X_pow]
      simp
    · intro b hb h_ne
      rw [coeff_C_mul_X_pow]
      simp [h_ne.symm]
    · intro h_not_in
      exfalso
      rw [Finset.mem_range] at h_not_in
      omega
  · apply Finset.sum_eq_zero
    intro b hb
    rw [Finset.mem_range] at hb
    rw [coeff_C_mul_X_pow]
    split_ifs with h_eq
    · omega
    · rfl

lemma apery_poly_int_natDegree (n : ℕ) : (apery_poly_int n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [apery_poly_int_coeff n m]
    have : ¬ m ≤ n := by omega
    simp [this]
  · rw [apery_poly_int_coeff n n]
    simp only [le_refl, choose_self, one_pow, one_mul, ne_eq]
    have h_pos : 1 ≤ (n + n).choose n := choose_pos (by omega)
    have h_cast : (1 : ℤ) ≤ (( (n + n).choose n : ℕ) : ℤ) := by exact_mod_cast h_pos
    have h_nz : (( (n + n).choose n : ℕ) : ℤ) ≠ 0 := by omega
    exact h_nz

lemma map_apery_poly_int_prime (n : ℕ) (hp : Fact (n+1).Prime) :
    map (Int.castRingHom (ZMod (n+1))) (apery_poly_int n) = 1 := by
  dsimp [apery_poly_int]
  rw [Polynomial.map_sum]
  rw [Finset.sum_range_succ']
  have h_sum : Finset.sum (Finset.range n) (fun k ↦ map (Int.castRingHom (ZMod (n + 1))) (C (((n.choose (k + 1) : ℤ) ^ 2 * ((n + (k + 1)).choose (k + 1) : ℤ))) * X ^ (k + 1))) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_range] at hk
    have hk1 : k + 1 ≤ n := by omega
    have hdvd : (n + 1) ∣ apery_coeff n (k + 1) := by
      apply apery_coeff_dvd n (k+1) (n+1) hp.out
      · omega
      · omega
      · omega
    have h_coeff : (((n.choose (k + 1)) ^ 2 * ((n + (k + 1)).choose (k + 1)) : ℕ) : ZMod (n + 1)) = 0 := by
      change (apery_coeff n (k+1) : ZMod (n+1)) = 0
      exact (CharP.cast_eq_zero_iff (ZMod (n + 1)) (n + 1) (apery_coeff n (k+1))).mpr hdvd
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]
    change C (((n.choose (k + 1)) ^ 2 * ((n + (k + 1)).choose (k + 1)) : ℕ) : ZMod (n + 1)) * X ^ (k + 1) = 0
    rw [h_coeff]
    simp
  rw [h_sum, add_zero]
  simp

lemma padicValNat_choose_two_mul (n : ℕ) (hp : Fact (n+1).Prime) (hn4 : n ≥ 4) :
    padicValNat (n+1) (choose (2*n) n) = 1 := by
  have h_log : log (n+1) (n + n) < 2 := by
    apply log_lt_of_lt_pow
    · omega
    · have : (n+1)^2 = n^2 + 2*n + 1 := by ring
      omega
  have h_val := padicValNat_choose' (p := n+1) h_log
  have h_2n : 2 * n = n + n := by ring
  rw [h_2n]
  rw [h_val]
  have h_ico : Finset.Ico 1 2 = {1} := rfl
  rw [h_ico]
  have h_cond : (n+1)^1 ≤ n % (n+1)^1 + n % (n+1)^1 := by
    simp only [pow_one]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have h_filter : Finset.filter (fun (i : ℕ) ↦ (n + 1) ^ i ≤ n % (n + 1) ^ i + n % (n + 1) ^ i) {1} = {1} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro h
      exact h.1
    · intro h
      rw [h]
      exact ⟨rfl, h_cond⟩
  rw [h_filter]
  rfl

lemma IsPrimitive_of_coeff_zero_eq_one (g : ℤ[X]) (h : g.coeff 0 = 1) : g.IsPrimitive := by
  intro r hdvd
  have hd : r ∣ g.coeff 0 := by
    rcases hdvd with ⟨q, rfl⟩
    rw [coeff_C_mul]
    exact dvd_mul_right r (coeff q 0)
  rw [h] at hd
  exact isUnit_of_dvd_one hd

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

theorem apery_poly_int_prime_irreducible (n : ℕ) (hp : Fact (n+1).Prime) (hn4 : n ≥ 4) :
    Irreducible (apery_poly_int n) := by
  constructor
  · intro h_unit
    rw [isUnit_iff] at h_unit
    rcases h_unit with ⟨r, hr, h_eq⟩
    have h_coeff : coeff (apery_poly_int n) n = coeff (C r) n := by
      exact congrArg (coeff · n) h_eq.symm
    rw [apery_poly_int_coeff n n] at h_coeff
    simp only [le_refl, choose_self, one_pow, one_mul] at h_coeff
    have h_coeff_C : coeff (C r) n = 0 := by
      have : n ≠ 0 := by omega
      rw [coeff_C]
      split_ifs with h_zero
      · omega
      · rfl
    rw [h_coeff_C] at h_coeff
    have h_2n : 2 * n = n + n := by ring
    have h_pos : 1 ≤ (n+n).choose n := by
      rw [← h_2n]
      exact choose_pos (by omega)
    have h_cast : (((n+n).choose n : ℕ) : ℤ) ≠ 0 := by
      exact_mod_cast (ne_of_gt h_pos)
    exact h_cast h_coeff
  · intro g h h_mul
    have h_deg : natDegree (map (Int.castRingHom (ZMod (n+1))) (apery_poly_int n)) < 1 := by
      rw [map_apery_poly_int_prime n hp]
      simp
    have h_c0 : (apery_poly_int n).coeff 0 = 1 := apery_poly_int_coeff_zero n
    have h_lc : ¬ (n+1 : ℤ) ^ 2 ∣ (apery_poly_int n).leadingCoeff := by
      rw [leadingCoeff, apery_poly_int_natDegree n]
      rw [apery_poly_int_coeff n n]
      simp only [le_refl, choose_self, one_pow, one_mul]
      have h_2n : 2 * n = n + n := by ring
      rw [← h_2n]
      intro hdvd
      have h_nz : choose (2 * n) n ≠ 0 := by
        have : 1 ≤ choose (2 * n) n := choose_pos (by omega)
        omega
      have h_padic : 2 ≤ padicValNat (n+1) (choose (2 * n) n) := by
        rw [← padicValNat_dvd_iff_le h_nz]
        exact_mod_cast hdvd
      have h_val := padicValNat_choose_two_mul n hp hn4
      omega
    have h_rest := proper_factor_degree_restriction (apery_poly_int n) g h 1 h_mul h_deg h_c0 h_lc
    rcases h_rest with hg | hh
    · left
      have hg0 : g.natDegree = 0 := by omega
      have h_eq : g = C (coeff g 0) := eq_C_of_natDegree_eq_zero hg0
      have hdvd : C (coeff g 0) ∣ apery_poly_int n := by
        rw [← h_eq]
        exact ⟨h, h_mul⟩
      have hprim : IsPrimitive (apery_poly_int n) := IsPrimitive_of_coeff_zero_eq_one (apery_poly_int n) h_c0
      have h_unit_coeff : IsUnit (coeff g 0) := hprim (coeff g 0) hdvd
      rw [h_eq]
      exact isUnit_C.mpr h_unit_coeff
    · right
      have hh0 : h.natDegree = 0 := by omega
      have h_eq : h = C (coeff h 0) := eq_C_of_natDegree_eq_zero hh0
      have hdvd : C (coeff h 0) ∣ apery_poly_int n := by
        rw [← h_eq]
        exact ⟨g, by rw [h_mul, mul_comm]⟩
      have hprim : IsPrimitive (apery_poly_int n) := IsPrimitive_of_coeff_zero_eq_one (apery_poly_int n) h_c0
      have h_unit_coeff : IsUnit (coeff h 0) := hprim (coeff h 0) hdvd
      rw [h_eq]
      exact isUnit_C.mpr h_unit_coeff
