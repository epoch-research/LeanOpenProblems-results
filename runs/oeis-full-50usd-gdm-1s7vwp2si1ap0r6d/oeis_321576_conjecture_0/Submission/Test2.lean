import FormalConjectures.Util.ProblemImports

open Nat Set ZMod

lemma general_prime_factor_gt_n (n : ℕ) (hn : n > 1) (b : ℕ) (hb : b = (n !)^2 + 1) (q : ℕ) (hq_prime : q.Prime) (hdvd : q ∣ b^n - (b-1)^n) :
    q > n := by
  by_contra hc
  have hq_le : q ≤ n := by omega
  have hq_dvd_fact : q ∣ n ! := Nat.dvd_factorial (hq_prime.pos) hq_le
  have hq_dvd_fact2 : q ∣ (n !)^2 := by
    rw [pow_two]
    exact dvd_mul_of_dvd_left hq_dvd_fact (n !)
  have hb_eq : b = (n !)^2 + 1 := hb
  have hq_dvd_b_sub_one : q ∣ b - 1 := by
    have : b - 1 = (n !)^2 := by omega
    rw [this]
    exact hq_dvd_fact2
  rcases hq_dvd_b_sub_one with ⟨k, hk⟩
  have hb_eq2 : b = q * k + 1 := by omega
  have h_zmod_b : (b : ZMod q) = 1 := by
    rw [hb_eq2]
    push_cast
    have hq0 : (q : ZMod q) = 0 := ZMod.natCast_self q
    rw [hq0]
    ring
  have h_zmod_b_sub_one : ((b - 1 : ℕ) : ZMod q) = 0 := by
    have : b - 1 = q * k := by omega
    rw [this]
    push_cast
    have hq0 : (q : ZMod q) = 0 := ZMod.natCast_self q
    rw [hq0]
    ring
  have hdvd_zmod : ((b^n - (b-1)^n : ℕ) : ZMod q) = 0 := by
    have : q ∣ b^n - (b-1)^n := hdvd
    rcases this with ⟨m, hm⟩
    rw [hm]
    push_cast
    have hq0 : (q : ZMod q) = 0 := ZMod.natCast_self q
    rw [hq0]
    ring
  have h_le : (b-1)^n ≤ b^n := Nat.pow_le_pow_left (by omega) n
  have h_sub_cast : ((b^n - (b-1)^n : ℕ) : ZMod q) = (b : ZMod q)^n - (((b-1 : ℕ) : ZMod q))^n := by
    rw [Nat.cast_sub h_le]
    push_cast
    rfl
  rw [hdvd_zmod] at h_sub_cast
  rw [h_zmod_b, h_zmod_b_sub_one] at h_sub_cast
  have h_one_pow : (1 : ZMod q)^n = 1 := one_pow n
  have h_zero_pow : (0 : ZMod q)^n = 0 := by
    exact zero_pow (by omega)
  rw [h_one_pow, h_zero_pow] at h_sub_cast
  simp at h_sub_cast
  have hq_gt1 : q > 1 := Nat.Prime.one_lt hq_prime
  have : Fact (1 < q) := ⟨hq_gt1⟩
  have h_ne : (0 : ZMod q) ≠ 1 := zero_ne_one
  exact h_ne h_sub_cast

lemma divisors_of_b_modEq_one_aux (n : ℕ) (hn : n > 1) (b : ℕ) (hb : b = (n !)^2 + 1) (d : ℕ) :
    d ∣ b^n - (b-1)^n → d ≡ 1 [MOD n] := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd
    by_cases hd0 : d = 0
    · subst hd0
      have h_pow : (b-1)^n < b^n := Nat.pow_lt_pow_left (by omega) (by omega)
      have : b^n - (b-1)^n = 0 := Nat.eq_zero_of_zero_dvd hd
      omega
    · by_cases hd1 : d = 1
      · subst hd1
        exact Nat.ModEq.refl 1
      · rcases Nat.exists_prime_and_dvd hd1 with ⟨q, hq_prime, hqd⟩
        have hqdvd : q ∣ b^n - (b-1)^n := dvd_trans hqd hd
        -- We want to prove q ≡ 1 [MOD n]
        sorry



