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

theorem rule_prime_power (p : ℕ) (hp : Nat.Prime p) (n : ℕ) (h_mod : n % (p * (p^2 + 1)) = 0) (h_ge : n ≥ 9) : a n > 0 := by
  let c := p^2 + 1
  let k := n / c
  have hc_pos : 0 < c := by omega
  have h_div : n = c * k := by
    have hc_dvd : c ∣ n := by
      have h_div_mul : p * c ∣ n := by
        exact Nat.dvd_of_mod_eq_zero h_mod
      exact dvd_of_mul_left_dvd h_div_mul
    exact (Nat.mul_div_cancel' hc_dvd).symm
  have hk_dvdp : p ∣ k := by
    have h_div_mul : p * c ∣ n := exact Nat.dvd_of_mod_eq_zero h_mod
    -- Since n = c * k and p * c ∣ n, we have p * c ∣ c * k, so p ∣ k
    rcases h_div_mul with ⟨m, hm⟩
    have hm2 : c * k = c * (p * m) := by
      omega
    have hk_eq : k = p * m := Nat.eq_of_mul_eq_mul_left hc_pos hm2
    exact Dvd.intro m hk_eq.symm
  have hk1 : 1 ≤ k := by
    -- n >= 9, and since n = c * k, we need to show k >= 1.
    -- If k = 0, n = 0, contradiction.
    by_contra h_lt
    have hk0 : k = 0 := by omega
    subst hk0
    omega
  have hk2 : k < (n - 1) / 2 + 1 := by
    -- We want to show k < (c * k - 1) / 2 + 1
    -- Since c = p^2 + 1 >= 5 (as p >= 2 since p is prime), c * k >= 5 * k.
    -- Then (5*k - 1) / 2 + 1 > k is true for k >= 1.
    have hp_ge2 : p ≥ 2 := Nat.Prime.two_le hp
    have hc_ge5 : c ≥ 5 := by
      have : p^2 ≥ 4 := by
        have : p * p ≥ 2 * 2 := Nat.mul_le_mul hp_ge2 hp_ge2 (by omega) (by omega)
        exact this
      omega
    omega
  have h_nk : n - k = p^2 * k := by
    have h_c : c = p^2 + 1 := rfl
    omega
  have hsq : sqrt (totient k * totient (n - k)) ^ 2 = totient k * totient (n - k) := by
    rw [h_nk]
    have h_tot_pk : totient (p * k) = p * totient k := totient_mul_of_prime_of_dvd hp hk_dvdp
    have h_tot_p2k : totient (p^2 * k) = p^2 * totient k := by
      have h_p2k : p^2 * k = p * (p * k) := by ring
      rw [h_p2k]
      have h_dvd : p ∣ p * k := dvd_mul_right p k
      rw [totient_mul_of_prime_of_dvd hp h_dvd]
      rw [h_tot_pk]
      ring
    rw [h_tot_p2k]
    have h_sq : totient k * (p^2 * totient k) = (p * totient k) ^ 2 := by ring
    rw [h_sq]
    rw [Nat.sqrt_eq']
  exact a_pos_of_exists n k hk1 hk2 hsq
