import Mathlib

def P : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 =>
    let (x, y) := P n
    (x - (n + 1) * y, (n + 1) * x + y)

theorem P_norm_pos (n : ℕ) : (P n).1^2 + (P n).2^2 > 0 := by
  induction n with
  | zero =>
    simp [P]
  | succ n ih =>
    simp [P]
    have h_eq : (P (n + 1)).1^2 + (P (n + 1)).2^2 = (1 + ((n + 1 : ℕ) : ℤ)^2) * ((P n).1^2 + (P n).2^2) := by
      simp [P]
      ring
    rw [h_eq]
    have h_sq_pos : 1 + ((n + 1 : ℕ) : ℤ)^2 > 0 := by
      have : ((n + 1 : ℕ) : ℤ)^2 ≥ 0 := sq_nonneg _
      omega
    exact mul_pos h_sq_pos ih

theorem valuation_one_add_sq_even (m : ℤ) (h : m % 2 = 0) : padicValInt 2 (1 + m^2) = 0 := by
  unfold padicValInt
  apply padicValNat.eq_zero_of_not_dvd
  intro hc
  have h_dvd : (2 : ℤ) ∣ (1 + m^2) := by
    rwa [← Int.ofNat_dvd_left] at hc
  have h_mod : (1 + m^2) % 2 = 1 := by
    have hm : m = 2 * (m / 2) := by omega
    set k := m / 2
    rw [hm]
    have : 1 + (2 * k)^2 = 2 * (2 * k^2) + 1 := by ring
    rw [this]
    omega
  have h_hc : (1 + m^2) % 2 = 0 := Int.dvd_iff_emod_eq_zero.mp h_dvd
  omega

theorem valuation_one_add_sq_odd (m : ℤ) (h : m % 2 = 1) : padicValInt 2 (1 + m^2) = 1 := by
  have h_prime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_eq : 1 + m^2 = 2 * (2 * (m / 2)^2 + 2 * (m / 2) + 1) := by
    have : m = 2 * (m / 2) + 1 := by omega
    nth_rw 1 [this]
    ring
  have h_odd : ¬ (2 : ℤ) ∣ (2 * (m / 2)^2 + 2 * (m / 2) + 1) := by
    intro hc
    rcases hc with ⟨d, hd⟩
    omega
  have h_eq_zero : padicValInt 2 (2 * (m / 2)^2 + 2 * (m / 2) + 1) = 0 := by
    unfold padicValInt
    apply padicValNat.eq_zero_of_not_dvd
    intro hc
    apply h_odd
    rwa [← Int.ofNat_dvd_left] at hc
  rw [h_eq]
  rw [padicValInt.mul]
  · have h2 : padicValInt 2 2 = 1 := by
      unfold padicValInt
      norm_num
    rw [h2, h_eq_zero, add_zero]
  · norm_num
  · intro hc
    have h_mod : (2 * (m / 2)^2 + 2 * (m / 2) + 1) % 2 = 1 := by
      set k := m / 2
      have : 2 * k^2 + 2 * k + 1 = 2 * (k^2 + k) + 1 := by ring
      rw [this]
      omega
    rw [hc] at h_mod
    norm_num at h_mod

theorem valuation_one_add_sq (m : ℤ) : padicValInt 2 (1 + m^2) = if m % 2 = 0 then 0 else 1 := by
  by_cases h : m % 2 = 0
  · rw [if_pos h]
    exact valuation_one_add_sq_even m h
  · have h_odd : m % 2 = 1 := by omega
    rw [if_neg h]
    exact valuation_one_add_sq_odd m h_odd

theorem valuation_P_norm (n : ℕ) : padicValInt 2 ((P n).1^2 + (P n).2^2) = (n + 1) / 2 := by
  induction n with
  | zero =>
    simp [P, valuation_one_add_sq]
  | succ n ih =>
    have h_eq : (P (n + 1)).1^2 + (P (n + 1)).2^2 = (1 + ((n + 1 : ℕ) : ℤ)^2) * ((P n).1^2 + (P n).2^2) := by
      simp [P]
      ring
    rw [h_eq]
    rw [padicValInt.mul]
    · have h_val : padicValInt 2 (1 + ((n + 1 : ℕ) : ℤ)^2) = if (n + 1) % 2 = 0 then 0 else 1 := by
        rw [valuation_one_add_sq (n + 1 : ℤ)]
        have h_mod : (n + 1 : ℤ) % 2 = ↑((n + 1) % 2) := by simp
        rw [h_mod]
        split_ifs with h1 h2 h2
        · rfl
        · exfalso; omega
        · exfalso; omega
        · rfl
      rw [h_val, ih]
      split_ifs with h
      · have : (n + 1) % 2 = 0 := h
        omega
      · have : (n + 1) % 2 = 1 := by omega
        omega
    · have : 1 + ((n + 1 : ℕ) : ℤ)^2 ≥ 1 := by
        have : ((n + 1 : ℕ) : ℤ)^2 ≥ 0 := sq_nonneg _
        omega
      omega
    · exact ne_of_gt (P_norm_pos n)
