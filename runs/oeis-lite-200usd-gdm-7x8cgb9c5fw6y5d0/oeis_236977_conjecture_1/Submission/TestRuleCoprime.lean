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

theorem rule_coprime (c : ℕ) (hc_sq : sqrt (totient c) ^ 2 = totient c) (hc_ge2 : c ≥ 2)
    (n : ℕ) (h_div : (c + 1) ∣ n) (h_coprime : Coprime c (n / (c + 1))) (h_ge : n ≥ 9) : a n > 0 := by
  have h_div_init' : n = (c + 1) * (n / (c + 1)) := (Nat.mul_div_cancel' h_div).symm
  generalize h_k : n / (c + 1) = k at h_div_init' h_coprime
  have h_div_init : n = (c + 1) * k := h_div_init'
  have hk1 : 1 ≤ k := by
    by_contra h_lt
    have hk0 : k = 0 := by omega
    have hn0 : n = 0 := by
      rw [h_div_init, hk0, mul_zero]
    omega
  have hk2 : k < (n - 1) / 2 + 1 := by
    have hc_ge3 : c + 1 ≥ 3 := by omega
    have hn_ge : n ≥ 3 * k := by
      rw [h_div_init]
      nlinarith
    omega
  have h_nk : n - k = c * k := by
    rw [h_div_init]
    rw [Nat.add_mul]
    rw [one_mul]
    rw [Nat.add_sub_cancel]
  have hsq : sqrt (totient k * totient (n - k)) ^ 2 = totient k * totient (n - k) := by
    rw [h_nk]
    rw [totient_mul h_coprime]
    have h_rew : totient c = sqrt (totient c) ^ 2 := hc_sq.symm
    rw [h_rew]
    have h_sq : totient k * (sqrt (totient c) ^ 2 * totient k) = (sqrt (totient c) * totient k) ^ 2 := by ring
    rw [h_sq]
    rw [Nat.sqrt_eq']
  exact a_pos_of_exists n k hk1 hk2 hsq
