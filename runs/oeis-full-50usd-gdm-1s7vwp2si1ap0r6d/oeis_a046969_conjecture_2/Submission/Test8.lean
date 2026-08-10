import FormalConjectures.Util.ProblemImports

open Rat Nat

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let m := 2 * n
    let k := m * (m - 1)
    (bernoulli m / (k : ℚ)).den

lemma a_num_den_relation (n : ℕ) (hn : 2 ≤ n) : (bernoulli (2 * n)).num * (a n : ℤ) = (bernoulli (2 * n) / ((2 * n * (2 * n - 1) : ℕ) : ℚ)).num * (bernoulli (2 * n)).den * ((2 * n * (2 * n - 1) : ℕ) : ℤ) := by
  unfold a
  have h_ne : n ≠ 0 := by omega
  simp only [h_ne, ↓reduceIte]
  let m := 2 * n
  let k := m * (m - 1)
  have hk_pos : 0 < k := by
    change 0 < (2 * n) * (2 * n - 1)
    apply Nat.mul_pos
    · omega
    · omega
  have hk_ne : (k : ℚ) ≠ 0 := by
    exact_mod_cast hk_pos.ne'
  let q := bernoulli m
  let r := (k : ℚ)⁻¹
  have hr_num : r.num = 1 := by
    exact inv_natCast_num_of_pos hk_pos
  have hr_den : r.den = k := by
    exact inv_natCast_den_of_pos hk_pos
  have h_mul := Rat.mul_num_den' q r
  rw [hr_num, hr_den] at h_mul
  simp only [mul_one] at h_mul
  have h_div : q * r = q / (k : ℚ) := by
    exact div_eq_mul_inv q (k : ℚ)
  rw [h_div] at h_mul
  have h_mul_int : q.num * ((q / (k : ℚ)).den : ℤ) = ((q / (k : ℚ)).num * (q.den : ℤ) * (k : ℤ) : ℤ) := by
    rw [h_mul]
  exact h_mul_int

lemma dvd_a_mul (n : ℕ) (hn : 2 ≤ n) : ((2 * n * (2 * n - 1) : ℕ) : ℤ) ∣ (bernoulli (2 * n)).num * (a n : ℤ) := by
  rw [a_num_den_relation n hn]
  use (bernoulli (2 * n) / ((2 * n * (2 * n - 1) : ℕ) : ℚ)).num * (bernoulli (2 * n)).den
  ring

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
    rw [← h_mul]
    ring
  have h_dvd_nat : k ∣ q.num.natAbs * (q / (k : ℚ)).den := by
    have h_abs : (q.num * ((q / (k : ℚ)).den : ℤ)).natAbs = q.num.natAbs * (q / (k : ℚ)).den := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]
    have h_dvd_abs : (k : ℤ).natAbs ∣ (q.num * ((q / (k : ℚ)).den : ℤ)).natAbs := by
      exact Int.natAbs_dvd_natAbs.mpr h_dvd
    rwa [Int.natAbs_natCast, h_abs] at h_dvd_abs
  let g := Nat.gcd q.num.natAbs k
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right _ hk
  have h_g_dvd : g ∣ k := Nat.gcd_dvd_right q.num.natAbs k
  have h_g_dvd_num : g ∣ q.num.natAbs := Nat.gcd_dvd_left q.num.natAbs k
  have h_eq_k : k = g * (k / g) := by rw [Nat.mul_div_cancel' h_g_dvd]
  have h_eq_num : q.num.natAbs = g * (q.num.natAbs / g) := by rw [Nat.mul_div_cancel' h_g_dvd_num]
  have h_dvd_nat' : g * (k / g) ∣ g * (q.num.natAbs / g) * (q / (k : ℚ)).den := by
    rw [h_eq_k.symm, h_eq_num.symm]
    exact h_dvd_nat
  rw [mul_assoc] at h_dvd_nat'
  have h_dvd_cancel : (k / g) ∣ (q.num.natAbs / g) * (q / (k : ℚ)).den := by
    rwa [mul_dvd_mul_iff_left hg_pos.ne'] at h_dvd_nat'
  have h_coprime : (q.num.natAbs / g).Coprime (k / g) := Nat.coprime_div_gcd_div_gcd hg_pos
  have h_coprime' : (k / g).Coprime (q.num.natAbs / g) := h_coprime.symm
  exact h_coprime'.dvd_of_dvd_mul_left h_dvd_cancel


lemma den_dvd_a (n : ℕ) (hn : 2 ≤ n) : ((bernoulli (2 * n)).den : ℤ) ∣ (a n : ℤ) := by
  have h_rel := a_num_den_relation n hn
  have h_dvd : ((bernoulli (2 * n)).den : ℤ) ∣ (bernoulli (2 * n)).num * (a n : ℤ) := by
    use (bernoulli (2 * n) / ((2 * n * (2 * n - 1) : ℕ) : ℚ)).num * ((2 * n * (2 * n - 1) : ℕ) : ℤ)
    rw [h_rel]
    ring
  have h_dvd_nat : (bernoulli (2 * n)).den ∣ (bernoulli (2 * n)).num.natAbs * a n := by
    have h_abs : ((bernoulli (2 * n)).num * (a n : ℤ)).natAbs = (bernoulli (2 * n)).num.natAbs * a n := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]
    have h_dvd_abs : ((bernoulli (2 * n)).den : ℤ).natAbs ∣ ((bernoulli (2 * n)).num * (a n : ℤ)).natAbs := by
      exact Int.natAbs_dvd_natAbs.mpr h_dvd
    rwa [Int.natAbs_natCast, h_abs] at h_dvd_abs
  have h_coprime : Nat.Coprime (bernoulli (2 * n)).num.natAbs (bernoulli (2 * n)).den := (bernoulli (2 * n)).reduced
  have h_coprime' : (bernoulli (2 * n)).den.Coprime (bernoulli (2 * n)).num.natAbs := h_coprime.symm
  have h_dvd_nat_final : (bernoulli (2 * n)).den ∣ a n := by
    exact h_coprime'.dvd_of_dvd_mul_left h_dvd_nat
  exact_mod_cast h_dvd_nat_final

