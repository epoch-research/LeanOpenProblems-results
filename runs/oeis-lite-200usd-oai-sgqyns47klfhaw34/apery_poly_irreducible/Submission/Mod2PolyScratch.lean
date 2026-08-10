import FormalConjectures.Util.ProblemImports
open Nat Polynomial

noncomputable def apery_poly_int (n : ℕ) : ℤ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℤ) * (X : ℤ[X]) ^ k

lemma choose_mul_choose_add_eq (n k : ℕ) (hk : k ≤ n) :
    (n + k).choose (2 * k) * (2 * k).choose k = (n + k).choose k * n.choose k := by
  have hsk : k ≤ 2 * k := by omega
  have h := Nat.choose_mul (n := n + k) (k := 2 * k) (s := k) hsk
  simpa [Nat.add_sub_cancel, Nat.mul_sub_right_distrib, hk, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc, two_mul] using h

lemma two_dvd_apery_coeff_nat (n k : ℕ) (hk0 : 0 < k) (hkn : k ≤ n) :
    2 ∣ (n.choose k) ^ 2 * ((n + k).choose k) := by
  have hcentral : 2 ∣ (2 * k).choose k := by
    simpa [Nat.centralBinom_eq_two_mul_choose] using Nat.two_dvd_centralBinom_of_one_le (n := k) hk0
  rcases hcentral with ⟨t, ht⟩
  use t * (n + k).choose (2 * k) * n.choose k
  have hid := choose_mul_choose_add_eq n k hkn
  calc
    (n.choose k) ^ 2 * ((n + k).choose k)
        = ((n + k).choose k * n.choose k) * n.choose k := by ring
    _ = ((n + k).choose (2 * k) * (2 * k).choose k) * n.choose k := by rw [hid]
    _ = ((n + k).choose (2 * k) * (2 * t)) * n.choose k := by rw [ht]
    _ = 2 * (t * (n + k).choose (2 * k) * n.choose k) := by ring

lemma apery_poly_int_coeff (n k : ℕ) :
    (apery_poly_int n).coeff k = (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℤ) := by
  by_cases hk : k ≤ n
  · rw [apery_poly_int, finset_sum_coeff]
    rw [Finset.sum_eq_single k]
    · rw [coeff_C_mul_X_pow]; simp
    · intro b hb hbne
      rw [coeff_C_mul_X_pow]
      rw [if_neg (by intro h; exact hbne h.symm)]
    · intro hnot
      exact False.elim (hnot (by simp only [Finset.mem_range]; exact Nat.lt_succ_of_le hk))
  · have hnk : n < k := Nat.lt_of_not_ge hk
    rw [apery_poly_int, finset_sum_coeff]
    trans 0
    · apply Finset.sum_eq_zero
      intro b hb
      rw [coeff_C_mul_X_pow]
      rw [if_neg]
      intro h
      subst h
      simp only [Finset.mem_range] at hb
      omega
    · simp [Nat.choose_eq_zero_of_lt hnk]

lemma apery_poly_int_mod_two (n : ℕ) :
    (apery_poly_int n).map (Int.castRingHom (ZMod 2)) = (1 : (ZMod 2)[X]) := by
  ext k
  rw [coeff_map, apery_poly_int_coeff]
  by_cases hk0 : k = 0
  · subst hk0
    simp
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    by_cases hkn : k ≤ n
    · have hdiv := two_dvd_apery_coeff_nat n k hkpos hkn
      have hzero : (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ZMod 2) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).2 hdiv
      rw [show (Int.castRingHom (ZMod 2)) (↑(((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℤ)) = 0 by
        change (((((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℤ) : ZMod 2) = 0)
        simpa using hzero]
      simp [Polynomial.coeff_one, hk0]
    · have hnk : n < k := Nat.lt_of_not_ge hkn
      simp [Nat.choose_eq_zero_of_lt hnk, Polynomial.coeff_one, hk0]
