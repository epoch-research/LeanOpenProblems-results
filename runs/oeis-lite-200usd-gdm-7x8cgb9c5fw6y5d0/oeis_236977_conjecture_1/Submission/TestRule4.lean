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

theorem rule_4 (n : ℕ) (h_mod : n % 30 = 0) (h_ge : n ≥ 9) : a n > 0 := by
  let k := n / 10
  have h_div : n = 10 * k := by
    have h10 : 10 ∣ n := by
      have h30 : n % 30 = 0 := h_mod
      omega
    exact (Nat.mul_div_cancel' h10).symm
  have hk_dvd3 : 3 ∣ k := by
    have h30 : n % 30 = 0 := h_mod
    have h_eq : k = n / 10 := rfl
    omega
  have hk1 : 1 ≤ k := by
    omega
  have hk2 : k < (n - 1) / 2 + 1 := by
    omega
  have h_nk : n - k = 9 * k := by
    omega
  have hsq : sqrt (totient k * totient (n - k)) ^ 2 = totient k * totient (n - k) := by
    rw [h_nk]
    have h_tot_3k : totient (3 * k) = 3 * totient k := by
      have h3 : Nat.Prime 3 := by decide
      exact totient_mul_of_prime_of_dvd h3 hk_dvd3
    have h_tot_9k : totient (9 * k) = 9 * totient k := by
      have h_9k : 9 * k = 3 * (3 * k) := by ring
      rw [h_9k]
      have h3 : Nat.Prime 3 := by decide
      have h_dvd : 3 ∣ 3 * k := dvd_mul_right 3 k
      rw [totient_mul_of_prime_of_dvd h3 h_dvd]
      rw [h_tot_3k]
      ring
    rw [h_tot_9k]
    have h_sq : totient k * (9 * totient k) = (3 * totient k) ^ 2 := by ring
    rw [h_sq]
    rw [Nat.sqrt_eq']
  exact a_pos_of_exists n k hk1 hk2 hsq
