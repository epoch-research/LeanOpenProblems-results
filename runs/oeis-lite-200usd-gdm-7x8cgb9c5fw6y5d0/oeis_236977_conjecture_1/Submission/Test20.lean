import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  (Ico 1 ((n - 1) / 2 + 1)).sum fun k =>
    let m := totient k * totient (n - k)
    if sqrt m ^ 2 = m then 1 else 0

theorem a_pos_of_exists (n : ℕ) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < (n - 1) / 2 + 1)
    (hsq : sqrt (totient k * totient (n - k)) ^ 2 = totient k * totient (n - k)) : a n > 0 := by
  have hk : k ∈ Ico 1 ((n - 1) / 2 + 1) := mem_Ico.2 ⟨hk1, hk2⟩
  have h_le : (if sqrt (totient k * totient (n - k)) ^ 2 = totient k * totient (n - k) then 1 else 0) ≤ a n := by
    apply single_le_sum (fun i _ => Nat.zero_le _) hk
  rw [hsq] at h_le
  simp only [if_true] at h_le
  exact h_le

theorem rule_1 (n : ℕ) (h_mod : n % 6 = 3) (h_ge : n ≥ 9) : a n > 0 := by
  let k := n / 3
  have h_div : n = 3 * k := by
    have h3 : 3 ∣ n := by
      have h6 : n % 6 = 3 := h_mod
      omega
    exact (Nat.mul_div_cancel' h3).symm
  have hk_mod : k % 2 = 1 := by
    have h_mod' : n % 6 = 3 := h_mod
    omega
  have hk_odd : Odd k := odd_iff.mpr hk_mod
  have hk1 : 1 ≤ k := by
    omega
  have hk2 : k < (n - 1) / 2 + 1 := by
    omega
  have h_nk : n - k = 2 * k := by
    omega
  have hsq : sqrt (totient k * totient (n - k)) ^ 2 = totient k * totient (n - k) := by
    rw [h_nk]
    have h_coprime : Coprime 2 k := coprime_two_left.mpr hk_odd
    have h_tot : totient (2 * k) = totient k := by
      rw [totient_mul h_coprime, totient_two, one_mul]
    rw [h_tot]
    have h_sq : totient k * totient k = (totient k) ^ 2 := by ring
    rw [h_sq]
    rw [Nat.sqrt_eq']
  exact a_pos_of_exists n k hk1 hk2 hsq

theorem rule_2 (n : ℕ) (h_mod : n % 10 = 0) (h_ge : n ≥ 9) : a n > 0 := by
  let k := n / 5
  have h_div : n = 5 * k := by
    have h5 : 5 ∣ n := by
      have h10 : n % 10 = 0 := h_mod
      omega
    exact (Nat.mul_div_cancel' h5).symm
  have hk_even : Even k := by
    have h_mod' : n % 10 = 0 := h_mod
    have h_eq : k = n / 5 := rfl
    use k / 2
    omega
  have hk1 : 1 ≤ k := by
    omega
  have hk2 : k < (n - 1) / 2 + 1 := by
    omega
  have h_nk : n - k = 4 * k := by
    omega
  have hsq : sqrt (totient k * totient (n - k)) ^ 2 = totient k * totient (n - k) := by
    rw [h_nk]
    have h_even2 : Even (2 * k) := by
      use k
      ring
    have h_tot4 : totient (4 * k) = 4 * totient k := by
      have h4k : 4 * k = 2 * (2 * k) := by ring
      rw [h4k]
      rw [totient_two_mul_of_even h_even2]
      rw [totient_two_mul_of_even hk_even]
      ring
    rw [h_tot4]
    have h_sq : totient k * (4 * totient k) = (2 * totient k) ^ 2 := by ring
    rw [h_sq]
    rw [Nat.sqrt_eq']
  exact a_pos_of_exists n k hk1 hk2 hsq

theorem rule_3 (n : ℕ) (h_mod6 : n % 6 = 0) (h_mod30 : n % 30 ≠ 0) (h_ge : n ≥ 9) : a n > 0 := by
  let k := n / 6
  have h_div : n = 6 * k := by
    have h6 : 6 ∣ n := Nat.dvd_of_mod_eq_zero h_mod6
    exact (Nat.mul_div_cancel' h6).symm
  have hk_not_dvd : ¬ 5 ∣ k := by
    intro hdvd
    have h30 : 30 ∣ n := by
      have h_k : n = 6 * k := h_div
      rcases hdvd with ⟨d, hd⟩
      use d
      omega
    have h_zero : n % 30 = 0 := Nat.mod_eq_zero_of_dvd h30
    exact h_mod30 h_zero
  have hk1 : 1 ≤ k := by
    omega
  have hk2 : k < (n - 1) / 2 + 1 := by
    omega
  have h_nk : n - k = 5 * k := by
    omega
  have hsq : sqrt (totient k * totient (n - k)) ^ 2 = totient k * totient (n - k) := by
    rw [h_nk]
    have h_p5 : Nat.Prime 5 := by decide
    have h_coprime : Coprime 5 k := (h_p5.coprime_iff_not_dvd).mpr hk_not_dvd
    have h_tot5 : totient (5 * k) = 4 * totient k := by
      rw [totient_mul h_coprime]
      have h_tot5_val : totient 5 = 4 := by decide
      rw [h_tot5_val]
    rw [h_tot5]
    have h_sq : totient k * (4 * totient k) = (2 * totient k) ^ 2 := by ring
    rw [h_sq]
    rw [Nat.sqrt_eq']
  exact a_pos_of_exists n k hk1 hk2 hsq
