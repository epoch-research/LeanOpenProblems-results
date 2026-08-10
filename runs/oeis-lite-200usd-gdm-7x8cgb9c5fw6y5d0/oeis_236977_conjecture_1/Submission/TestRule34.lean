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

theorem rule_34 (n : ℕ) (h_mod : n % 34 = 0) (h_ge : n ≥ 9) : a n > 0 := by
  let k := n / 17
  have h_div : n = 17 * k := by
    have h17 : 17 ∣ n := by
      have h34 : n % 34 = 0 := h_mod
      omega
    exact (Nat.mul_div_cancel' h17).symm
  have hk_even : Even k := by
    have h34 : n % 34 = 0 := h_mod
    have h_eq : k = n / 17 := rfl
    use k / 2
    omega
  have hk1 : 1 ≤ k := by
    omega
  have hk2 : k < (n - 1) / 2 + 1 := by
    omega
  have h_nk : n - k = 16 * k := by
    omega
  have hsq : sqrt (totient k * totient (n - k)) ^ 2 = totient k * totient (n - k) := by
    rw [h_nk]
    have h_even2 : Even (2 * k) := by
      use k
      ring
    have h_even4 : Even (4 * k) := by
      use 2 * k
      ring
    have h_even8 : Even (8 * k) := by
      use 4 * k
      ring
    have h_tot16 : totient (16 * k) = 16 * totient k := by
      have h16k : 16 * k = 2 * (8 * k) := by ring
      have h8k : 8 * k = 2 * (4 * k) := by ring
      have h4k : 4 * k = 2 * (2 * k) := by ring
      have h2k : 2 * k = 2 * k := by ring
      rw [h16k, totient_two_mul_of_even h_even8]
      rw [h8k, totient_two_mul_of_even h_even4]
      rw [h4k, totient_two_mul_of_even h_even2]
      rw [h2k, totient_two_mul_of_even hk_even]
      ring
    rw [h_tot16]
    have h_sq : totient k * (16 * totient k) = (4 * totient k) ^ 2 := by ring
    rw [h_sq]
    rw [Nat.sqrt_eq']
  exact a_pos_of_exists n k hk1 hk2 hsq
