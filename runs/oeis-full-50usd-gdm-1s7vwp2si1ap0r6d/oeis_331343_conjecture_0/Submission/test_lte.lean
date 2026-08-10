import FormalConjectures.Util.ProblemImports

open Nat

lemma fermat_two_dvd {p : ℕ} (hp_prime : p.Prime) (hp3 : p ≥ 3) : p ∣ 2^(p - 1) - 1 := by
  have h_not_div : ¬ p ∣ 2 := by
    intro hc
    have : p ≤ 2 := Nat.le_of_dvd (by decide) hc
    omega
  have h_cop : Nat.Coprime 2 p := by
    rw [Nat.coprime_comm]
    exact hp_prime.coprime_iff_not_dvd.mpr h_not_div
  have h_mod := Nat.pow_card_sub_one_sub_one_mod_card hp_prime h_cop
  exact Nat.dvd_of_mod_eq_zero h_mod


lemma pow_mul_relation (p k : ℕ) (hk : k ≥ 1) (hp3 : p ≥ 3) :
    (2^(p - 1))^((p^k - 1) / (p - 1)) - 1 = 2^(p^k - 1) - 1 := by
  have hdvd : p - 1 ∣ p^k - 1 := Nat.sub_one_dvd_pow_sub_one p k
  rw [← pow_mul]
  have h_mul : (p - 1) * ((p^k - 1) / (p - 1)) = p^k - 1 := Nat.mul_div_cancel' hdvd
  rw [h_mul]


lemma p_odd_lemma {p : ℕ} (hp_prime : p.Prime) (hp3 : p ≥ 3) : Odd p :=
  hp_prime.odd_of_ne_two (by omega)


lemma emultiplicity_pow_eq_self {p k : ℕ} (hp_prime : p.Prime) (hp3 : p ≥ 3) (hk : k ≥ 1) :
    emultiplicity p (2^(p^k - 1) - 1) = emultiplicity p (2^(p - 1) - 1) := by
  let x := 2^(p - 1)
  let y := 1
  let M := (p^k - 1) / (p - 1)
  have hp_odd : Odd p := hp_prime.odd_of_ne_two (by omega)
  have h_dvd : p ∣ x - y := fermat_two_dvd hp_prime hp3
  have h_not_dvd : ¬ p ∣ x := by
    intro hc
    have h_prime_dvd := hp_prime.dvd_of_dvd_pow hc
    have : p ≤ 2 := Nat.le_of_dvd (by decide) h_prime_dvd
    omega
  have h_lte := Nat.emultiplicity_pow_sub_pow hp_prime hp_odd h_dvd h_not_dvd M
  have h_eq : x^M - y^M = 2^(p^k - 1) - 1 := pow_mul_relation p k hk hp3
  rw [h_eq] at h_lte
  have h_not_p_dvd_M : ¬ p ∣ M := by
    intro hc
    have hdvd : p - 1 ∣ p^k - 1 := Nat.sub_one_dvd_pow_sub_one p k
    have h_div_M : M * (p - 1) = p^k - 1 := Nat.mul_div_cancel' hdvd
    have h_p_dvd_sub : p ∣ p^k - 1 := by
      rw [← h_div_M]
      exact dvd_mul_of_dvd_left hc (p - 1)
    have h_p_dvd_pk : p ∣ p^k := by
      have : k = (k - 1) + 1 := by omega
      rw [this, pow_succ]
      exact dvd_mul_left p (p^(k-1))
    have h_p_dvd_one : p ∣ p^k - (p^k - 1) := Nat.dvd_sub (by omega) h_p_dvd_pk h_p_dvd_sub
    have : p^k - (p^k - 1) = 1 := by omega
    rw [this] at h_p_dvd_one
    have : p ≤ 1 := Nat.le_of_dvd (by decide) h_p_dvd_one
    omega
  have h_emult_M : emultiplicity p M = 0 := by
    rw [Nat.emultiplicity_eq_zero]
    exact h_not_p_dvd_M
  rw [h_emult_M, add_zero] at h_lte
  exact h_lte
