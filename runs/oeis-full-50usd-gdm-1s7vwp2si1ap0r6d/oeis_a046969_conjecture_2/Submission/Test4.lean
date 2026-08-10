import FormalConjectures.Util.ProblemImports

lemma odd_num_of_even_den (q : ℚ) (h : 2 ∣ q.den) : ¬ (2 : ℤ) ∣ q.num := by
  intro h_div
  have h_div_nat : 2 ∣ q.num.natAbs := by
    exact Int.natAbs_dvd_natAbs.mpr h_div
  have h_gcd : 2 ∣ q.num.natAbs.gcd q.den := by
    exact Nat.dvd_gcd h_div_nat h
  have h_coprime : Nat.Coprime q.num.natAbs q.den := q.reduced
  rw [h_coprime] at h_gcd
  contradiction

lemma den_div_helper (q : ℚ) (k : ℕ) (hk : 0 < k) :
    (k / Nat.gcd q.num.natAbs k) ∣ (q / (k : ℚ)).den := by
  let r := (k : ℚ)⁻¹
  have hr_num : r.num = 1 := by
    exact Rat.inv_natCast_num_of_pos hk
  have hr_den : r.den = k := by
    exact Rat.inv_natCast_den_of_pos hk
  have h_mul := Rat.mul_num_den' q r
  rw [hr_num, hr_den] at h_mul
  simp only [mul_one] at h_mul
  have h_div : q * r = q / (k : ℚ) := by
    exact div_eq_mul_inv q (k : ℚ)
  rw [h_div] at h_mul
  have h_dvd : (k : ℤ) ∣ q.num * ((q / (k : ℚ)).den : ℤ) := by
    use (q / (k : ℚ)).num * q.den
    rw [h_mul]
    ring
  have h_dvd_nat : k ∣ q.num.natAbs * (q / (k : ℚ)).den := by
    have h_abs : (q.num * ((q / (k : ℚ)).den : ℤ)).natAbs = q.num.natAbs * (q / (k : ℚ)).den := by
      rw [Int.natAbs_mul, Int.natAbs_cast]
    have h_dvd_abs : (k : ℤ).natAbs ∣ (q.num * ((q / (k : ℚ)).den : ℤ)).natAbs := by
      exact Int.natAbs_dvd_natAbs.mpr h_dvd
    rwa [Int.natAbs_cast, h_abs] at h_dvd_abs
  let g := Nat.gcd q.num.natAbs k
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right _ hk
  have h_g_dvd : g ∣ k := Nat.gcd_dvd_right q.num.natAbs k
  have h_g_dvd_num : g ∣ q.num.natAbs := Nat.gcd_dvd_left q.num.natAbs k
  have h_eq_k : k = g * (k / g) := by rw [Nat.mul_div_cancel' h_g_dvd]
  have h_eq_num : q.num.natAbs = g * (q.num.natAbs / g) := by rw [Nat.mul_div_cancel' h_g_dvd_num]
  rw [h_eq_k, h_eq_num, mul_assoc] at h_dvd_nat
  have h_dvd_cancel : (k / g) ∣ (q.num.natAbs / g) * (q / (k : ℚ)).den := by
    rwa [mul_dvd_mul_iff_left hg_pos] at h_dvd_nat
  have h_coprime : (q.num.natAbs / g).Coprime (k / g) := by
    exact (Nat.coprime_div_gcd_div_gcd hg_pos).symm
  exact h_coprime.dvd_of_dvd_mul_right h_dvd_cancel
