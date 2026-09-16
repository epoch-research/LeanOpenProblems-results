import Mathlib

open Nat ZMod

theorem one_add_mul_pow_eq_one_add_mul_of_sq_eq_zero {R : Type*} [CommRing R] (p : R) (hp : p ^ 2 = 0) (k : ℕ) :
    (1 + p) ^ k = 1 + k * p := by
  induction' k with k ih
  · simp
  · rw [pow_succ, ih]
    calc (1 + (k : R) * p) * (1 + p)
      _ = 1 + p + k * p + k * p^2 := by ring
      _ = 1 + p + k * p + k * 0 := by rw [hp]
      _ = 1 + (k + 1 : R) * p := by ring
      _ = 1 + (k + 1 : ℕ) * p := by push_cast; rfl

theorem prime_power_contradiction {p k n : ℕ} (hp : p.Prime) (hk : 2 ≤ k)
    (hm : p ^ k = 2 * n + 1)
    (h_pseudo : ∀ x : ZMod (p ^ k), IsUnit x → x ^ n = 1 ∨ x ^ n = -1) : False := by
  have h_dvd : p ^ 2 ∣ p ^ k := pow_dvd_pow p hk
  let f : ZMod (p ^ k) →+* ZMod (p ^ 2) := ZMod.castHom h_dvd (ZMod (p ^ 2))
  have h_coprime : Coprime (1 + p) (p ^ k) := by
    have h1 : Coprime (1 + p) p := Nat.coprime_add_self_left.mpr (Nat.coprime_one_left p)
    exact h1.pow_right k
  have hx_unit : IsUnit (1 + (p : ZMod (p ^ k))) := by
    have : (1 + (p : ZMod (p ^ k))) = ((1 + p : ℕ) : ZMod (p ^ k)) := by push_cast; rfl
    rw [this]
    exact (ZMod.isUnit_iff_coprime (1+p) (p^k)).mpr h_coprime
  rcases h_pseudo (1 + (p : ZMod (p ^ k))) hx_unit with h1 | h2
  · have hf1 : f ((1 + (p : ZMod (p ^ k))) ^ n) = f 1 := congrArg f h1
    simp only [map_pow, map_add, map_one, map_natCast] at hf1
    have hp2 : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
      have : (p : ZMod (p ^ 2)) ^ 2 = ((p ^ 2 : ℕ) : ZMod (p ^ 2)) := by push_cast; rfl
      rw [this]
      exact ZMod.natCast_self (p ^ 2)
    have h_binom := one_add_mul_pow_eq_one_add_mul_of_sq_eq_zero (p : ZMod (p ^ 2)) hp2 n
    rw [h_binom] at hf1
    have h_np : (n : ZMod (p ^ 2)) * p = 0 := by
      calc (n : ZMod (p ^ 2)) * p = 1 + n * p - 1 := by ring
        _ = 1 - 1 := by rw [hf1]
        _ = 0 := by ring
    have h_dvd2 : p ^ 2 ∣ n * p := by
      rw [← CharP.cast_eq_zero_iff (ZMod (p ^ 2)) (p ^ 2)]
      have : ((n * p : ℕ) : ZMod (p ^ 2)) = (n : ZMod (p ^ 2)) * p := by push_cast; rfl
      rw [this]
      exact h_np
    have h_dvd_n : p ∣ n := by
      cases' h_dvd2 with c hc
      have hc2 : (p * c) * p = n * p := by
        calc (p * c) * p = p ^ 2 * c := by ring
          _ = n * p := hc.symm
      have h_pos : p > 0 := hp.pos
      have hc3 : p * c = n := Nat.eq_of_mul_eq_mul_right h_pos hc2
      exact ⟨c, hc3.symm⟩
    have hm_eq : p ^ k = 2 * n + 1 := hm
    have hp_dvd_pk : p ∣ p ^ k := dvd_pow_self p (by omega)
    have hp_dvd_2n : p ∣ 2 * n := dvd_mul_of_dvd_right h_dvd_n 2
    have hp_dvd_1 : p ∣ 1 := by
      have h_diff : 1 = p ^ k - 2 * n := by omega
      rw [h_diff]
      exact Nat.dvd_sub hp_dvd_pk hp_dvd_2n
    exact Nat.Prime.not_dvd_one hp hp_dvd_1
  · have hf1 : f ((1 + (p : ZMod (p ^ k))) ^ n) = f (-1) := congrArg f h2
    simp only [map_pow, map_add, map_one, map_natCast, map_neg] at hf1
    have hp2 : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
      have : (p : ZMod (p ^ 2)) ^ 2 = ((p ^ 2 : ℕ) : ZMod (p ^ 2)) := by push_cast; rfl
      rw [this]
      exact ZMod.natCast_self (p ^ 2)
    have h_binom := one_add_mul_pow_eq_one_add_mul_of_sq_eq_zero (p : ZMod (p ^ 2)) hp2 n
    rw [h_binom] at hf1
    have h_2_np : (2 : ZMod (p ^ 2)) + (n : ZMod (p ^ 2)) * p = 0 := by
      calc (2 : ZMod (p ^ 2)) + (n : ZMod (p ^ 2)) * p = 1 + n * p + 1 := by ring
        _ = -1 + 1 := by rw [hf1]
        _ = 0 := by ring
    have h_dvd2 : p ^ 2 ∣ 2 + n * p := by
      rw [← CharP.cast_eq_zero_iff (ZMod (p ^ 2)) (p ^ 2)]
      have : (((2 + n * p) : ℕ) : ZMod (p ^ 2)) = 2 + (n : ZMod (p ^ 2)) * p := by push_cast; rfl
      rw [this]
      exact h_2_np
    have hp_dvd_p2 : p ∣ p ^ 2 := dvd_pow_self p (by omega)
    have hp_dvd_2_np : p ∣ 2 + n * p := dvd_trans hp_dvd_p2 h_dvd2
    have hp_dvd_np : p ∣ n * p := dvd_mul_left p n
    have hp_dvd_2 : p ∣ 2 := by
      have h_diff : 2 = 2 + n * p - n * p := by omega
      rw [h_diff]
      exact Nat.dvd_sub hp_dvd_2_np hp_dvd_np
    have hp_le : p ≤ 2 := Nat.le_of_dvd zero_lt_two hp_dvd_2
    have hp_eq_2 : p = 2 := by
      -- since p is prime, p >= 2
      have hp2 : p ≥ 2 := hp.two_le
      omega
    subst hp_eq_2
    have h_even : Even (2 ^ k) := by
      exact even_pow.mpr ⟨even_two, by omega⟩
    have h_odd : Odd (2 ^ k) := by
      have : 2 ^ k = 2 * n + 1 := hm
      rw [this]
      exact odd_two_mul_add_one n
    rcases h_even with ⟨a, ha⟩
    rcases h_odd with ⟨b, hb⟩
    omega
