import FormalConjectures.Util.ProblemImports


noncomputable def a (n : ℕ) : ℕ :=
  if h_n : n > 0 then
    let S_n : Set ℕ :=
      { b | b > 1 ∧
          let k := b ^ n - (b - 1) ^ n -- Note: This is natural number subtraction. For n > 1 and b >= 2, b^n > (b-1)^n.
          ∀ (d : ℕ), d ∣ k → d ≡ 1 [MOD n] }
    -- sInf finds the smallest element of a set in a partial order, which is the minimum for $\mathbb{N}$.
    sInf S_n
  else
    0

open Set
open Nat

lemma sInf_eq_two_of_mem_of_lower_bound (S : Set ℕ) (h2 : 2 ∈ S) (hl : ∀ b ∈ S, 2 ≤ b) : sInf S = 2 := by
  have h_le : sInf S ≤ 2 := Nat.sInf_le h2
  have h_mem : sInf S ∈ S := Nat.sInf_mem ⟨2, h2⟩
  have h_ge : 2 ≤ sInf S := hl (sInf S) h_mem
  omega

lemma a_eq_sInf (n : ℕ) (h_n : n > 1) :
  a n = sInf { b | b > 1 ∧ ∀ (d : ℕ), d ∣ (b ^ n - (b - 1) ^ n) → d ≡ 1 [MOD n] } := by
  dsimp [a]
  split_ifs with h
  · rfl
  · omega



lemma a_eq_two_iff (n : ℕ) (h_n : n > 1) :
  a n = 2 ↔ ∀ (d : ℕ), d ∣ (2 ^ n - 1) → d ≡ 1 [MOD n] := by
  rw [a_eq_sInf n h_n]
  let S := { b | b > 1 ∧ ∀ (d : ℕ), d ∣ (b ^ n - (b - 1) ^ n) → d ≡ 1 [MOD n] }
  have hS : S = { b | b > 1 ∧ ∀ (d : ℕ), d ∣ (b ^ n - (b - 1) ^ n) → d ≡ 1 [MOD n] } := rfl
  have h_two_sub_one : 2 - 1 = 1 := by omega
  have h_one_pow : 1 ^ n = 1 := one_pow n
  have h_two_pow : 2 ^ n - (2 - 1) ^ n = 2 ^ n - 1 := by rw [h_two_sub_one, h_one_pow]
  constructor
  · intro h
    have h_pos : 0 < sInf S := by rw [h]; decide
    have h_nonempty : S.Nonempty := Nat.nonempty_of_pos_sInf h_pos
    have h_mem : sInf S ∈ S := Nat.sInf_mem h_nonempty
    rw [h] at h_mem
    change 2 > 1 ∧ ∀ (d : ℕ), d ∣ (2 ^ n - (2 - 1) ^ n) → d ≡ 1 [MOD n] at h_mem
    rw [h_two_pow] at h_mem
    exact h_mem.2
  · intro h
    have h2 : 2 ∈ S := by
      change 2 > 1 ∧ ∀ (d : ℕ), d ∣ (2 ^ n - (2 - 1) ^ n) → d ≡ 1 [MOD n]
      rw [h_two_pow]
      exact ⟨by omega, h⟩
    have hl : ∀ b ∈ S, 2 ≤ b := by
      intro b hb
      change b > 1 ∧ _ at hb
      omega
    exact sInf_eq_two_of_mem_of_lower_bound S h2 hl



lemma odd_mersenne {p : ℕ} (hp : p > 0) : Odd (2^p - 1) := by
  have h1 : 2^p = 2 * 2^(p-1) := by
    nth_rw 1 [show p = p - 1 + 1 by omega]
    rw [pow_succ]
    ring
  have h2 : 2^(p-1) ≥ 1 := Nat.one_le_pow _ _ (by decide)
  use 2^(p-1) - 1
  omega

lemma q_ne_two {p q : ℕ} (hp : p.Prime) (hdvd : q ∣ 2^p - 1) : q ≠ 2 := by
  intro hq
  subst hq
  have h_dvd : 2 ∣ 2^p - 1 := hdvd
  have h_odd : Odd (2^p - 1) := odd_mersenne hp.pos
  have h_not_even : ¬ Even (2^p - 1) := Nat.not_even_iff_odd.mpr h_odd
  have h_even_dvd : Even (2^p - 1) := even_iff_two_dvd.mpr h_dvd
  contradiction




lemma prime_factor_of_mersenne_mod_eq_one {p : ℕ} (hp : p.Prime) {q : ℕ} (hq : q.Prime) (hdvd : q ∣ 2^p - 1) : q ≡ 1 [MOD p] := by
  have : Fact q.Prime := ⟨hq⟩
  have hq_ne_two : q ≠ 2 := q_ne_two hp hdvd
  have ha0 : (2 : ZMod q) ≠ 0 := by
    rw [Ne, ← Nat.cast_two, ZMod.natCast_eq_zero_iff]
    intro h_dvd
    have hq2 : q = 1 ∨ q = 2 := (Nat.dvd_prime Nat.prime_two).mp h_dvd
    rcases hq2 with rfl | rfl
    · exact Nat.not_prime_one hq
    · exact hq_ne_two rfl
  have h_cast : ((2^p - 1 : ℕ) : ZMod q) = 0 := by
    rwa [ZMod.natCast_eq_zero_iff]
  have h_sub : ((2^p - 1 : ℕ) : ZMod q) = (2 : ZMod q)^p - 1 := by
    have h_le : 1 ≤ 2^p := Nat.one_le_pow _ _ (by decide)
    rw [Nat.cast_sub h_le, Nat.cast_pow, Nat.cast_two, Nat.cast_one]
  rw [h_sub] at h_cast
  have h_pow_eq_one : (2 : ZMod q)^p = 1 := by
    exact sub_eq_zero.mp h_cast
  have h_ord_dvd_p : orderOf (2 : ZMod q) ∣ p := orderOf_dvd_of_pow_eq_one h_pow_eq_one
  rcases (Nat.dvd_prime hp).mp h_ord_dvd_p with h_ord_one | h_ord_p
  · -- orderOf (2 : ZMod q) = 1
    have h_pow_one := pow_orderOf_eq_one (2 : ZMod q)
    rw [h_ord_one] at h_pow_one
    rw [pow_one] at h_pow_one
    have h_two_eq_one : (2 : ZMod q) = 1 := h_pow_one
    have h_char : (1 : ZMod q) = 0 := by
      calc (1 : ZMod q) = (2 : ZMod q) - 1 := by ring
      _ = 1 - 1 := by rw [h_two_eq_one]
      _ = 0 := by ring
    rw [← Nat.cast_one, ZMod.natCast_eq_zero_iff] at h_char
    have : q = 1 := Nat.dvd_one.mp h_char
    subst this
    exfalso
    exact Nat.not_prime_one hq
  · -- orderOf (2 : ZMod q) = p
    have h_dvd_card : orderOf (2 : ZMod q) ∣ q - 1 := ZMod.orderOf_dvd_card_sub_one ha0
    rw [h_ord_p] at h_dvd_card
    have hq_ge : 1 ≤ q := by have := hq.two_le; omega
    have h_mod_eq : 1 ≡ q [MOD p] := (Nat.modEq_iff_dvd' hq_ge).mpr h_dvd_card
    exact h_mod_eq.symm



lemma all_divisors_of_mersenne_mod_eq_one {p : ℕ} (hp : p.Prime) (d : ℕ) (hdvd : d ∣ 2^p - 1) : d ≡ 1 [MOD p] := by
  induction' d using Nat.strong_induction_on with d ih
  rcases eq_or_ne d 0 with rfl | hd_nz
  · -- d = 0
    exfalso
    have h_zero_dvd : 0 ∣ 2^p - 1 := hdvd
    have h_zero : 2^p - 1 = 0 := Nat.eq_zero_of_zero_dvd h_zero_dvd
    have h_pos : 2^p - 1 > 0 := by
      have : p > 0 := hp.pos
      have : 2^p ≥ 2^1 := Nat.pow_le_pow_right (by decide) this
      omega
    omega
  rcases eq_or_ne d 1 with rfl | hd_none
  · -- d = 1
    rfl
  · -- d > 1
    have hd_gt_one : d > 1 := by
      have : d ≥ 1 := Nat.pos_of_ne_zero hd_nz
      omega
    have : d ≠ 1 := hd_none
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd this
    obtain ⟨k, hk⟩ := hqdvd
    have hk_lt : k < d := by
      rw [hk]
      have hq_gt_one : 1 < q := hq.one_lt
      have hk_pos : 0 < k := by
        by_contra h_zero
        have : k = 0 := by omega
        subst this
        rw [mul_zero] at hk
        omega
      calc k = 1 * k := by ring
      _ < q * k := Nat.mul_lt_mul_of_pos_right hq_gt_one hk_pos
    have hk_dvd : k ∣ 2^p - 1 := by
      have h_div : k ∣ d := by
        use q
        rw [hk]
        ring
      exact dvd_trans h_div hdvd
    have hq_dvd : q ∣ 2^p - 1 := by
      have h_div : q ∣ d := by
        use k
      exact dvd_trans h_div hdvd
    have ih_k : k ≡ 1 [MOD p] := ih k hk_lt hk_dvd
    have hq_mod : q ≡ 1 [MOD p] := prime_factor_of_mersenne_mod_eq_one hp hq hq_dvd
    rw [hk]
    have h_mul := Nat.ModEq.mul hq_mod ih_k
    rw [mul_one] at h_mul
    exact h_mul



lemma a_eq_two_of_prime (n : ℕ) (h_n : n > 1) (hp : n.Prime) : a n = 2 := by
  rw [a_eq_two_iff n h_n]
  exact all_divisors_of_mersenne_mod_eq_one hp



lemma divisor_inequality {n : ℕ} (h_n : n > 1) (hc : ¬ n.Prime) (h_all : ∀ (d : ℕ), d ∣ (2^n - 1) → d ≡ 1 [MOD n]) :
  ∃ p c, p.Prime ∧ p = minFac n ∧ n = p * c ∧ c ≥ 2 ∧ p * c ≤ 2^p - 2 := by
  let p := minFac n
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have h_div : p ∣ n := Nat.minFac_dvd n
  have hp_lt : p < n := by
    rwa [← not_prime_iff_minFac_lt (by omega)]
  have hc_gt_one : n / p > 1 := by
    by_contra h_le
    have h_le' : n / p ≤ 1 := by omega
    have h_div_eq : n / p * p = n := Nat.div_mul_cancel h_div
    interval_cases h_val : n / p
    · omega
    · omega
  let c := n / p
  have hc_ge : c ≥ 2 := by omega
  have hc_eq : n = p * c := by
    rw [mul_comm]
    exact (Nat.div_mul_cancel h_div).symm
  use p, c
  refine ⟨hp, rfl, hc_eq, hc_ge, ?_⟩
  · have h_dvd_mersenne : 2^p - 1 ∣ 2^n - 1 := Nat.pow_sub_one_dvd_pow_sub_one 2 h_div
    have h_mod_eq : 2^p - 1 ≡ 1 [MOD n] := h_all (2^p - 1) h_dvd_mersenne
    have h_ge1 : 1 ≤ 2^p - 1 := by
      have : p ≥ 2 := hp.two_le
      have h_pow : 2^p ≥ 2^2 := Nat.pow_le_pow_right (by decide : 2 ≥ 1) this
      omega
    have h_mod_eq_symm : 1 ≡ 2^p - 1 [MOD n] := h_mod_eq.symm
    rw [Nat.modEq_iff_dvd' h_ge1] at h_mod_eq_symm
    have h_eq : (2^p - 1) - 1 = 2^p - 2 := by
      have : p ≥ 2 := hp.two_le
      have h_pow : 2^p ≥ 2^2 := Nat.pow_le_pow_right (by decide : 2 ≥ 1) this
      omega
    rw [h_eq] at h_mod_eq_symm
    have h_le_sub : n ≤ 2^p - 2 := by
      apply Nat.le_of_dvd _ h_mod_eq_symm
      have : p ≥ 2 := hp.two_le
      have h_pow : 2^p ≥ 2^2 := Nat.pow_le_pow_right (by decide : 2 ≥ 1) this
      omega
    rw [← hc_eq]
    exact h_le_sub



lemma ge_minFac_of_dvd {n c : ℕ} (h_n : n > 1) (hdvd : c ∣ n) (hc2 : c ≥ 2) : c ≥ minFac n := by
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd (by omega : c ≠ 1)
  have h_prime_dvd_n : q ∣ n := dvd_trans hqdvd hdvd
  have h_ge : q ≥ minFac n := Nat.minFac_le_of_dvd hq.two_le h_prime_dvd_n
  have h_le : q ≤ c := Nat.le_of_dvd (by omega) hqdvd
  omega




theorem oeis_321576_conjecture_prime_iff_val_two (n : ℕ) (h_n : n > 1) :
  a n = 2 ↔ Nat.Prime n := by
  constructor
  · intro ha
    by_contra hc
    rw [a_eq_two_iff n h_n] at ha
    obtain ⟨p, c, hp, hp_eq, h_eq, hc_ge, h_ineq⟩ := divisor_inequality h_n hc ha
    have hdvd_c : c ∣ n := by
      use p
      rw [mul_comm]
      exact h_eq
    have hc_ge_p : c ≥ p := by
      rw [hp_eq]
      exact ge_minFac_of_dvd h_n hdvd_c hc_ge
    have h_p2_le : p * p ≤ 2^p - 2 := by
      calc p * p ≤ p * c := Nat.mul_le_mul_left p hc_ge_p
      _ ≤ 2^p - 2 := h_ineq
    -- Now we have h_p2_le : p^2 ≤ 2^p - 2
    -- Let us show that p cannot be 2, 3, 5
    have hp_neq_two : p ≠ 2 := by
      intro h_two
      subst h_two
      omega
    have hp_neq_three : p ≠ 3 := by
      intro h_three
      subst h_three
      omega
    have hp_neq_five : p ≠ 5 := by
      intro h_five
      subst h_five
      have h_div_mersenne : 2^5 - 1 ∣ 2^n - 1 := by
        have : minFac n = 5 := hp_eq.symm
        rw [← this]
        exact Nat.pow_sub_one_dvd_pow_sub_one 2 (Nat.minFac_dvd n)
      have h_mod_eq : 2^5 - 1 ≡ 1 [MOD n] := ha (2^5 - 1) h_div_mersenne
      have h_ge1 : 1 ≤ 2^5 - 1 := by decide
      have h_mod_eq_symm : 1 ≡ 2^5 - 1 [MOD n] := h_mod_eq.symm
      rw [Nat.modEq_iff_dvd' h_ge1] at h_mod_eq_symm
      have h_eq_sub : (2^5 - 1) - 1 = 30 := by decide
      rw [h_eq_sub] at h_mod_eq_symm
      -- Now we have h_mod_eq_symm : n ∣ 30
      have hc_ge_five : c ≥ 5 := hc_ge_p
      have hc_le_six : c ≤ 6 := by omega
      interval_cases c
      · -- c = 5
        have hn_eq : n = 25 := by omega
        rw [hn_eq] at h_mod_eq_symm
        have : ¬ 25 ∣ 30 := by decide
        contradiction
      · -- c = 6
        have hn_eq : n = 30 := by omega
        have h_min : minFac 30 = 2 := by rfl
        have h_p_eq : minFac n = 5 := hp_eq.symm
        rw [hn_eq] at h_p_eq
        rw [h_min] at h_p_eq
        omega
    sorry
  · intro hp
    exact a_eq_two_of_prime n h_n hp
