import FormalConjectures.Util.ProblemImports
open Nat Polynomial

noncomputable def apery_recip_int (n : ℕ) : ℤ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (j : ℕ) ↦
    C (((n.choose j) ^ 2 * ((2 * n - j).choose (n - j)) : ℕ) : ℤ) * (X : ℤ[X]) ^ j

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

lemma apery_recip_coeff (n j : ℕ) :
    (apery_recip_int n).coeff j = (((n.choose j) ^ 2 * ((2 * n - j).choose (n - j)) : ℕ) : ℤ) := by
  by_cases hj : j ≤ n
  · rw [apery_recip_int, finset_sum_coeff]
    rw [Finset.sum_eq_single j]
    · rw [coeff_C_mul_X_pow]; simp
    · intro b hb hbne
      rw [coeff_C_mul_X_pow]
      rw [if_neg (by intro h; exact hbne h.symm)]
    · intro hnot
      exact False.elim (hnot (by simp only [Finset.mem_range]; exact Nat.lt_succ_of_le hj))
  · have hnj : n < j := Nat.lt_of_not_ge hj
    rw [apery_recip_int, finset_sum_coeff]
    trans 0
    · apply Finset.sum_eq_zero
      intro b hb
      rw [coeff_C_mul_X_pow]
      rw [if_neg]
      intro h
      subst h
      simp only [Finset.mem_range] at hb
      omega
    · simp [Nat.choose_eq_zero_of_lt hnj]

lemma apery_recip_mod_two (n : ℕ) :
    (apery_recip_int n).map (Int.castRingHom (ZMod 2)) = (X : (ZMod 2)[X]) ^ n := by
  ext j
  rw [coeff_map, apery_recip_coeff, coeff_X_pow]
  by_cases hjn : j = n
  · subst hjn
    simp
  · rw [if_neg hjn]
    by_cases hjle : j ≤ n
    · have hlt : j < n := lt_of_le_of_ne hjle hjn
      let k := n - j
      have hkpos : 0 < k := by dsimp [k]; omega
      have hkle : k ≤ n := by dsimp [k]; omega
      have hdivA := two_dvd_apery_coeff_nat n k hkpos hkle
      have hident : (n.choose j) ^ 2 * ((2 * n - j).choose (n - j)) =
          (n.choose k) ^ 2 * ((n + k).choose k) := by
        have hj_eq : j = n - k := by dsimp [k]; omega
        rw [hj_eq]
        have hchoose : n.choose (n - k) = n.choose k := Nat.choose_symm hkle
        have hsub : 2 * n - (n - k) = n + k := by omega
        have hsub2 : n - (n - k) = k := by omega
        simp [hchoose, hsub, hsub2]
      have hdiv : 2 ∣ (n.choose j) ^ 2 * ((2 * n - j).choose (n - j)) := by
        rwa [hident]
      have hzero : (((n.choose j) ^ 2 * ((2 * n - j).choose (n - j)) : ℕ) : ZMod 2) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).2 hdiv
      change (((((n.choose j) ^ 2 * ((2 * n - j).choose (n - j)) : ℕ) : ℤ) : ZMod 2) = 0)
      simpa using hzero
    · have hnj : n < j := Nat.lt_of_not_ge hjle
      simp [Nat.choose_eq_zero_of_lt hnj]
