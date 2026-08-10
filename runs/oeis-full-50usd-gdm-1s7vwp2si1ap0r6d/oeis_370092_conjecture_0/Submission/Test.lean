import FormalConjectures.Util.ProblemImports

open Nat

lemma le_pow_self_of_two_le (p e : ℕ) (hp : 2 ≤ p) : e ≤ p ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ]
    have h1 : p ^ e * 2 ≤ p ^ e * p := Nat.mul_le_mul_left (p ^ e) hp
    have h_one : 1 ≤ p ^ e := Nat.one_le_pow e p (by omega)
    have h3 : e + 1 ≤ p ^ e + p ^ e := by omega
    have h5 : p ^ e + p ^ e = p ^ e * 2 := by ring
    rw [h5] at h3
    exact h3.trans h1

lemma dvd_of_modEq_one {a m : ℕ} (hm : 2 ≤ m) (h : a ≡ 1 [MOD m]) : m ∣ a - 1 := by
  have h1 : 1 % m = 1 := Nat.mod_eq_of_lt (by omega)
  have h2 : a % m = 1 := by
    have h_eq : a % m = 1 % m := h
    rw [h_eq, h1]
  have h3 : a = m * (a / m) + a % m := (Nat.div_add_mod a m).symm
  rw [h2] at h3
  have h4 : a - 1 = m * (a / m) := by omega
  rw [h4]
  exact dvd_mul_right m (a / m)

lemma prime_power_dvd (p : ℕ) (hp : p.Prime) (e : ℕ) (g : ℕ) (n : ℕ) (hn : p^e ≤ n) :
    p^e ∣ g^n * (g ^ (totient (p^e)) - 1) := by
  by_cases he : e = 0
  · rw [he, pow_zero]
    exact one_dvd _
  · have h_pe_ge_two : 2 ≤ p^e := by
      rcases Nat.exists_eq_succ_of_ne_zero he with ⟨e', rfl⟩
      rw [pow_succ]
      have hp2 : 2 ≤ p := hp.two_le
      have h_one : 1 ≤ p ^ e' := Nat.one_le_pow e' p (by omega)
      have h_ge : p ≤ p ^ e' * p := by
        have h_mul : 1 * p ≤ p ^ e' * p := Nat.mul_le_mul_right p h_one
        rw [one_mul] at h_mul
        exact h_mul
      omega
    by_cases h_div : p ∣ g
    · rcases h_div with ⟨q, rfl⟩
      have h_pow : (p * q) ^ n = p ^ n * q ^ n := mul_pow p q n
      rw [h_pow]
      have h_le : e ≤ p ^ e := le_pow_self_of_two_le p e hp.two_le
      have h_en : e ≤ n := by omega
      have h_dvd_pn : p^e ∣ p^n := pow_dvd_pow p h_en
      have h_dvd_gn : p^e ∣ p^n * q^n := dvd_mul_of_dvd_left h_dvd_pn (q^n)
      exact dvd_mul_of_dvd_left h_dvd_gn _
    · have h_coprime_p : g.Coprime p := ((hp.coprime_iff_not_dvd).mpr h_div).symm
      have h_coprime_pe : g.Coprime (p^e) := h_coprime_p.pow_right e
      have h_modeq : g ^ (totient (p^e)) ≡ 1 [MOD p^e] := Nat.ModEq.pow_totient h_coprime_pe
      have h_dvd_diff : p^e ∣ g ^ (totient (p^e)) - 1 := dvd_of_modEq_one h_pe_ge_two h_modeq
      exact dvd_mul_of_dvd_right h_dvd_diff _

lemma k_dvd_of_prime_pow_dvd (g : ℕ) (k : ℕ) (n : ℕ) (hn : k ≤ n) :
    k ∣ g ^ n * (g ^ (totient k) - 1) := by
  by_cases hk : k = 0
  · rw [hk]
    exact dvd_zero _
  · rw [dvd_iff_prime_pow_dvd_dvd]
    intro p k' hp hp_dvd
    have h_le_k : p ^ k' ≤ k := Nat.le_of_dvd (by omega) hp_dvd
    have h_le_n : p ^ k' ≤ n := h_le_k.trans hn
    have h_dvd_p_pow : p ^ k' ∣ g ^ n * (g ^ (totient (p ^ k')) - 1) := prime_power_dvd p hp k' g n h_le_n
    have h_tot_dvd : totient (p ^ k') ∣ totient k := totient_dvd_of_dvd hp_dvd
    have h_sub_dvd : g ^ (totient (p ^ k')) - 1 ∣ g ^ (totient k) - 1 := pow_sub_one_dvd_pow_sub_one g h_tot_dvd
    have h_mul_dvd : g ^ n * (g ^ (totient (p ^ k')) - 1) ∣ g ^ n * (g ^ (totient k) - 1) := mul_dvd_mul_left (g ^ n) h_sub_dvd
    exact dvd_trans h_dvd_p_pow h_mul_dvd

lemma pow_add_totient_eq (k : ℕ) (g : ZMod k) (n : ℕ) (hn : k ≤ n) :
    g ^ (n + totient k) = g ^ n := by
  by_cases hk : k = 0
  · subst hk
    simp
  · have : NeZero k := ⟨hk⟩
    have h_val_eq : g = (g.val : ZMod k) := by
      apply ZMod.val_injective k
      rw [ZMod.val_natCast]
      rw [Nat.mod_eq_of_lt g.val_lt]
    rw [h_val_eq]
    rw [← Nat.cast_pow, ← Nat.cast_pow]
    rw [ZMod.natCast_eq_natCast_iff]
    rw [Nat.ModEq]
    rw [pow_add]
    have h_dvd : k ∣ g.val ^ n * g.val ^ totient k - g.val ^ n := by
      have h_factor : g.val ^ n * g.val ^ totient k - g.val ^ n = g.val ^ n * (g.val ^ totient k - 1) := by
        rw [Nat.mul_sub_left_distrib, mul_one]
      rw [h_factor]
      exact k_dvd_of_prime_pow_dvd g.val k n hn
    have h_le_pow : g.val ^ n ≤ g.val ^ n * g.val ^ totient k := by
      by_cases hg : g.val = 0
      · rw [hg]
        have hn1 : 1 ≤ n := by omega
        rw [zero_pow (by omega)]
        simp
      · have hg1 : 1 ≤ g.val := by omega
        have h_pow_pos : 1 ≤ g.val ^ totient k := Nat.one_le_pow _ _ hg1
        exact Nat.le_mul_of_pos_right _ h_pow_pos
    have h_eq : g.val ^ n * g.val ^ totient k ≡ g.val ^ n [MOD k] := by
      exact ((Nat.modEq_iff_dvd' h_le_pow).mpr h_dvd).symm
    exact h_eq



