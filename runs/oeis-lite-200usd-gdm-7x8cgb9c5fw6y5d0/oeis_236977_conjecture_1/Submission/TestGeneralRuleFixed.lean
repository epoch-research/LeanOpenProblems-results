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
  have hc_pos : 0 < c := by omega
  have hc_dvd : c ∣ n := by
    have h_div_mul : p * c ∣ n := Nat.dvd_of_mod_eq_zero h_mod
    exact dvd_of_mul_left_dvd h_div_mul
  have h_div_init : n = c * (n / c) := (Nat.mul_div_cancel' hc_dvd).symm
  generalize h_k : n / c = k at h_div_init
  have h_div : n = c * k := h_div_init
  have hk_dvdp : p ∣ k := by
    have h_div_mul : p * c ∣ n := Nat.dvd_of_mod_eq_zero h_mod
    rcases h_div_mul with ⟨m, hm⟩
    have hm2 : c * k = c * (p * m) := by
      rw [← h_div, hm]
      ring
    have hk_eq : k = p * m := Nat.eq_of_mul_eq_mul_left hc_pos hm2
    exact Dvd.intro m hk_eq.symm
  have hk1 : 1 ≤ k := by
    by_contra h_lt
    have hk0 : k = 0 := by omega
    have hn0 : n = 0 := by
      rw [h_div, hk0, mul_zero]
    omega
  have hk2 : k < (n - 1) / 2 + 1 := by
    have hp_ge2 : p ≥ 2 := Nat.Prime.two_le hp
    have hc_ge5 : c ≥ 5 := by
      have h_sq : p^2 ≥ 4 := by
        rw [Nat.pow_two]
        rcases p with _ | _ | p'
        · contradiction
        · contradiction
        · have : (p' + 2) * (p' + 2) ≥ 4 := by
            calc (p' + 2) * (p' + 2) = (p' + 2) * p' + (p' + 2) * 2 := by ring
            _ ≥ (p' + 2) * 2 := by omega
            _ = 2 * p' + 4 := by ring
            _ ≥ 4 := by omega
          exact this
      omega
    have hn_ge : n ≥ 5 * k := by
      rw [h_div]
      nlinarith
    omega
  have h_nk : n - k = p^2 * k := by
    rw [h_div]
    rw [Nat.add_mul]
    rw [one_mul]
    rw [Nat.add_sub_cancel]
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
