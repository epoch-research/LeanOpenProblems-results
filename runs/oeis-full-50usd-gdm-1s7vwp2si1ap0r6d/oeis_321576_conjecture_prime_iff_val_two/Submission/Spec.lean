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



lemma coprime_of_lt_minFac {n m : ℕ} (hn : n > 1) (hm_pos : m > 0) (hm : m < minFac n) : Nat.Coprime n m := by
  have h_gcd : Nat.gcd n m = 1 := by
    by_contra hg
    have hg_gt_1 : Nat.gcd n m > 1 := by
      have : Nat.gcd n m ≠ 0 := by
        intro h0
        have : n = 0 := Nat.eq_zero_of_gcd_eq_zero_left h0
        omega
      omega
    obtain ⟨s, hs_prime, h_s_dvd⟩ := Nat.exists_prime_and_dvd (by omega : Nat.gcd n m ≠ 1)
    have h_s_dvd_n : s ∣ n := dvd_trans h_s_dvd (Nat.gcd_dvd_left n m)
    have h_s_dvd_m : s ∣ m := dvd_trans h_s_dvd (Nat.gcd_dvd_right n m)
    have h_s_ge : s ≥ minFac n := Nat.minFac_le_of_dvd hs_prime.two_le h_s_dvd_n
    have h_s_le : s ≤ m := Nat.le_of_dvd (by omega) h_s_dvd_m
    omega
  exact h_gcd

lemma modEq_one_of_prime_factors (r : ℕ) (A : ℕ) (hA : A > 0) (h : ∀ u, u.Prime → u ∣ A → u ≡ 1 [MOD r]) : A ≡ 1 [MOD r] := by
  induction' A using Nat.strong_induction_on with A ih
  rcases eq_or_ne A 1 with rfl | hA1
  · rfl
  · have hA_gt_1 : A > 1 := by omega
    obtain ⟨u, hu, hudvd⟩ := Nat.exists_prime_and_dvd hA1
    obtain ⟨B, rfl⟩ := hudvd
    have h_u_mod : u ≡ 1 [MOD r] := h u hu (dvd_mul_right u B)
    have hB_pos : B > 0 := by
      by_contra hB0
      have : B = 0 := by omega
      subst this
      omega
    have hB_lt : B < u * B := by
      have : u ≥ 2 := hu.two_le
      calc B = 1 * B := by ring
      _ < u * B := Nat.mul_lt_mul_of_pos_right (by omega) hB_pos
    have h_B_mod : B ≡ 1 [MOD r] := by
      apply ih B hB_lt hB_pos
      intro v hv hvdvd
      apply h v hv
      exact dvd_mul_of_dvd_right hvdvd u
    have h_mul := Nat.ModEq.mul h_u_mod h_B_mod
    rw [mul_one] at h_mul
    exact h_mul



lemma divisor_inequality {n : ℕ} (h_n : n > 1) (hc : ¬ n.Prime) (h_all : ∀ (d : ℕ), d ∣ (2^n - 1) → d ≡ 1 [MOD n]) :
  ∃ p c, p.Prime ∧ p = minFac n ∧ n = p * c ∧ c ≥ 2 ∧ p * c ≤ 2^p - 2 ∧ n ∣ 2^p - 2 := by
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
    rw [hc_eq] at h_le_sub
    exact ⟨h_le_sub, h_mod_eq_symm⟩



lemma ge_minFac_of_dvd {n c : ℕ} (h_n : n > 1) (hdvd : c ∣ n) (hc2 : c ≥ 2) : c ≥ minFac n := by
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd (by omega : c ≠ 1)
  have h_prime_dvd_n : q ∣ n := dvd_trans hqdvd hdvd
  have h_ge : q ≥ minFac n := Nat.minFac_le_of_dvd hq.two_le h_prime_dvd_n
  have h_le : q ≤ c := Nat.le_of_dvd (by omega) hqdvd
  omega




theorem oeis_321576_conjecture_prime_iff_val_two (n : ℕ) (h_n : n > 1) :
  a n = 2 ↔ Nat.Prime n := by
  revert h_n
  induction' n using Nat.strong_induction_on with n ih
  intro h_n
  constructor
  · intro ha
    by_contra hc
    rw [a_eq_two_iff n h_n] at ha
    obtain ⟨p, c, hp, hp_eq, h_eq, hc_ge, h_ineq, h_dvd_sub⟩ := divisor_inequality h_n hc ha
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
    have hp_neq_seven : p ≠ 7 := by
      intro h_seven
      subst h_seven
      have hn_dvd : n ∣ 126 := by
        have : 2^7 - 2 = 126 := by rfl
        rw [← this]
        exact h_dvd_sub
      have hc_dvd_18 : c ∣ 18 := by
        have h_eq' : n = 7 * c := h_eq
        rw [h_eq'] at hn_dvd
        have h_126 : 126 = 7 * 18 := by rfl
        rw [h_126] at hn_dvd
        exact (mul_dvd_mul_iff_left (by decide)).mp hn_dvd
      have hc_ge_seven : c ≥ 7 := hc_ge_p
      have hc_vals : c = 9 ∨ c = 18 := by
        have hc_le_18 : c ≤ 18 := Nat.le_of_dvd (by decide) hc_dvd_18
        interval_cases c
        · exfalso; revert hc_dvd_18; decide
        · exfalso; revert hc_dvd_18; decide
        · exact Or.inl rfl
        · exfalso; revert hc_dvd_18; decide
        · exfalso; revert hc_dvd_18; decide
        · exfalso; revert hc_dvd_18; decide
        · exfalso; revert hc_dvd_18; decide
        · exfalso; revert hc_dvd_18; decide
        · exfalso; revert hc_dvd_18; decide
        · exfalso; revert hc_dvd_18; decide
        · exfalso; revert hc_dvd_18; decide
        · exact Or.inr rfl
      rcases hc_vals with rfl | rfl
      · have hn_eq : n = 63 := by omega
        have h_3_dvd_63 : 3 ∣ 63 := by decide
        have h_7_dvd_mersenne : 2^3 - 1 ∣ 2^63 - 1 := by
          rw [← hn_eq]
          exact Nat.pow_sub_one_dvd_pow_sub_one 2 (by rw [hn_eq]; decide)
        have h_7_eq : 2^3 - 1 = 7 := by rfl
        rw [h_7_eq] at h_7_dvd_mersenne
        have ha' := ha
        rw [hn_eq] at ha'
        have h_mod_eq : 7 ≡ 1 [MOD 63] := ha' 7 h_7_dvd_mersenne
        have h_ge1 : 1 ≤ 7 := by decide
        have h_mod_eq_symm : 1 ≡ 7 [MOD 63] := h_mod_eq.symm
        rw [Nat.modEq_iff_dvd' h_ge1] at h_mod_eq_symm
        have : (7 - 1) = 6 := by rfl
        rw [this] at h_mod_eq_symm
        have : 63 ∣ 6 := h_mod_eq_symm
        have : 63 ≤ 6 := Nat.le_of_dvd (by decide) this
        omega
      · have hn_eq : n = 126 := by omega
        have h_min : minFac 126 = 2 := by rfl
        have h_p_eq : minFac n = 7 := hp_eq.symm
        rw [hn_eq] at h_p_eq
        rw [h_min] at h_p_eq
        omega
    have hp_neq_eleven : p ≠ 11 := by
      intro h_eleven
      subst h_eleven
      have hn_dvd : n ∣ 2046 := by
        have : 2^11 - 2 = 2046 := by rfl
        rw [← this]
        exact h_dvd_sub
      have hc_dvd_186 : c ∣ 186 := by
        have h_eq' : n = 11 * c := h_eq
        rw [h_eq'] at hn_dvd
        have h_2046 : 2046 = 11 * 186 := by rfl
        rw [h_2046] at hn_dvd
        exact (mul_dvd_mul_iff_left (by decide)).mp hn_dvd
      have hc_ge_eleven : c ≥ 11 := hc_ge_p
      have hc_vals : c = 31 ∨ c = 62 ∨ c = 93 ∨ c = 186 := by
        have hc_le_186 : c ≤ 186 := Nat.le_of_dvd (by decide) hc_dvd_186
        interval_cases c
        all_goals (try exfalso; revert hc_dvd_186; decide)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
      rcases hc_vals with rfl | rfl | rfl | rfl
      · have hn_eq : n = 341 := by omega
        have h_23_dvd_mersenne : 23 ∣ 2^341 - 1 := by
          have h_div : 11 ∣ 341 := by decide
          have h_11_dvd_341 : 2^11 - 1 ∣ 2^341 - 1 := Nat.pow_sub_one_dvd_pow_sub_one 2 h_div
          have h_23_dvd_11 : 23 ∣ 2^11 - 1 := by decide
          exact dvd_trans h_23_dvd_11 h_11_dvd_341
        have ha' := ha
        rw [hn_eq] at ha'
        have h_mod_eq : 23 ≡ 1 [MOD 341] := ha' 23 h_23_dvd_mersenne
        have h_ge1 : 1 ≤ 23 := by decide
        have h_mod_eq_symm : 1 ≡ 23 [MOD 341] := h_mod_eq.symm
        rw [Nat.modEq_iff_dvd' h_ge1] at h_mod_eq_symm
        have : (23 - 1) = 22 := by rfl
        rw [this] at h_mod_eq_symm
        have : 341 ∣ 22 := h_mod_eq_symm
        have : 341 ≤ 22 := Nat.le_of_dvd (by decide) this
        omega
      · have hn_eq : n = 682 := by omega
        have h_min : minFac 682 = 2 := by rfl
        have h_p_eq : minFac n = 11 := hp_eq.symm
        rw [hn_eq] at h_p_eq
        rw [h_min] at h_p_eq
        omega
      · have hn_eq : n = 1023 := by omega
        have h_3_dvd_1023 : 3 ∣ 1023 := by decide
        have h_7_dvd_mersenne : 2^3 - 1 ∣ 2^1023 - 1 := by
          rw [← hn_eq]
          exact Nat.pow_sub_one_dvd_pow_sub_one 2 (by rw [hn_eq]; decide)
        have h_7_eq : 2^3 - 1 = 7 := by rfl
        rw [h_7_eq] at h_7_dvd_mersenne
        have ha' := ha
        rw [hn_eq] at ha'
        have h_mod_eq : 7 ≡ 1 [MOD 1023] := ha' 7 h_7_dvd_mersenne
        have h_ge1 : 1 ≤ 7 := by decide
        have h_mod_eq_symm : 1 ≡ 7 [MOD 1023] := h_mod_eq.symm
        rw [Nat.modEq_iff_dvd' h_ge1] at h_mod_eq_symm
        have : (7 - 1) = 6 := by rfl
        rw [this] at h_mod_eq_symm
        have : 1023 ∣ 6 := h_mod_eq_symm
        have : 1023 ≤ 6 := Nat.le_of_dvd (by decide) this
        omega
      · have hn_eq : n = 2046 := by omega
        have h_min : minFac 2046 = 2 := by rfl
        have h_p_eq : minFac n = 11 := hp_eq.symm
        rw [hn_eq] at h_p_eq
        rw [h_min] at h_p_eq
        omega
    have hp_neq_thirteen : p ≠ 13 := by
      intro h_thirteen
      subst h_thirteen
      have hn_dvd : n ∣ 8190 := by
        have : 2^13 - 2 = 8190 := by rfl
        rw [← this]
        exact h_dvd_sub
      have hc_dvd_630 : c ∣ 630 := by
        have h_eq' : n = 13 * c := h_eq
        rw [h_eq'] at hn_dvd
        have h_8190 : 8190 = 13 * 630 := by rfl
        rw [h_8190] at hn_dvd
        exact (mul_dvd_mul_iff_left (by decide)).mp hn_dvd
      have hc_ge_thirteen : c ≥ 13 := hc_ge_p
      by_cases hc_eq_one : c = 1
      · subst hc_eq_one
        omega
      · obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hc_eq_one
        have hr_dvd_630 : r ∣ 630 := dvd_trans hrdvd hc_dvd_630
        have hr_ge_thirteen : r ≥ 13 := by
          have hr_dvd_n : r ∣ n := by
            rw [h_eq]
            exact dvd_mul_of_dvd_right hrdvd 13
          have h_le := Nat.minFac_le_of_dvd hr.two_le hr_dvd_n
          rw [← hp_eq] at h_le
          exact h_le
        have h_dvd_mul : r ∣ 30 * 21 := by
          have : 630 = 30 * 21 := by rfl
          rwa [this] at hr_dvd_630
        rcases (Nat.Prime.dvd_mul hr).mp h_dvd_mul with hr_dvd_30 | hr_dvd_21
        · have hr_le_30 : r ≤ 30 := Nat.le_of_dvd (by decide) hr_dvd_30
          have hr_ge_13 : 13 ≤ r := hr_ge_thirteen
          interval_cases r <;> (exfalso; first | (revert hr_dvd_30; decide) | (revert hr; decide))
        · have hr_le_21 : r ≤ 21 := Nat.le_of_dvd (by decide) hr_dvd_21
          have hr_ge_13 : 13 ≤ r := hr_ge_thirteen
          interval_cases r <;> (exfalso; first | (revert hr_dvd_21; decide) | (revert hr; decide))
    have hp_neq_seventeen : p ≠ 17 := by
      intro h_seventeen
      subst h_seventeen
      have hn_dvd : n ∣ 131070 := by
        have : 2^17 - 2 = 131070 := by rfl
        rw [← this]
        exact h_dvd_sub
      have hc_dvd_7710 : c ∣ 7710 := by
        have h_eq' : n = 17 * c := h_eq
        rw [h_eq'] at hn_dvd
        have h_131070 : 131070 = 17 * 7710 := by rfl
        rw [h_131070] at hn_dvd
        exact (mul_dvd_mul_iff_left (by decide)).mp hn_dvd
      have hc_ge_seventeen : c ≥ 17 := hc_ge_p
      by_cases hc_eq_one : c = 1
      · subst hc_eq_one
        omega
      · obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hc_eq_one
        have hr_dvd_7710 : r ∣ 7710 := dvd_trans hrdvd hc_dvd_7710
        have hr_ge_seventeen : r ≥ 17 := by
          have hr_dvd_n : r ∣ n := by
            rw [h_eq]
            exact dvd_mul_of_dvd_right hrdvd 17
          have h_le := Nat.minFac_le_of_dvd hr.two_le hr_dvd_n
          rw [← hp_eq] at h_le
          exact h_le
        have hr_vals : r = 257 := by
          have h_dvd_mul : r ∣ 30 * 257 := by
            have : 7710 = 30 * 257 := by rfl
            rwa [this] at hr_dvd_7710
          rcases (Nat.Prime.dvd_mul hr).mp h_dvd_mul with hr_dvd_30 | hr_dvd_257
          · have hr_le_30 : r ≤ 30 := Nat.le_of_dvd (by decide) hr_dvd_30
            have hr_ge_17 : 17 ≤ r := hr_ge_seventeen
            interval_cases r <;> (exfalso; first | (revert hr_dvd_30; decide) | (revert hr; decide))
          · have h257 : Nat.Prime 257 := by set_option maxRecDepth 10000 in decide
            have hr_eq : r = 1 ∨ r = 257 := (Nat.dvd_prime h257).mp hr_dvd_257
            rcases hr_eq with rfl | rfl
            · exfalso; exact hr.ne_one rfl
            · rfl
        subst hr_vals
        have hc_eq_257 : c = 257 := by
          obtain ⟨k, hk⟩ := hrdvd
          have hk_dvd_30 : k ∣ 30 := by
            have : 17 * c ∣ 17 * 7710 := by
              rw [← h_eq]
              exact hn_dvd
            rw [hk] at hc_dvd_7710
            have : 257 * k ∣ 257 * 30 := by
              have h_7710 : 7710 = 257 * 30 := by rfl
              rw [h_7710] at hc_dvd_7710
              exact hc_dvd_7710
            exact (mul_dvd_mul_iff_left (by decide)).mp this
          have hk_le_30 : k ≤ 30 := Nat.le_of_dvd (by decide) hk_dvd_30
          have hk_eq_1 : k = 1 := by
            by_contra hk_ne_1
            obtain ⟨s, hs, hsdvd⟩ := Nat.exists_prime_and_dvd hk_ne_1
            have hs_dvd_30 : s ∣ 30 := dvd_trans hsdvd hk_dvd_30
            have hs_ge_17 : s ≥ 17 := by
              have hs_dvd_c : s ∣ c := by
                rw [hk]
                exact dvd_mul_of_dvd_right hsdvd 257
              have hr_dvd_n : s ∣ n := by
                rw [h_eq]
                exact dvd_mul_of_dvd_right hs_dvd_c 17
              have hp_eq' : 17 = minFac n := hp_eq
              rw [hp_eq']
              exact Nat.minFac_le_of_dvd hs.two_le hr_dvd_n
            have hs_le_five : s ≤ 5 := by
              have hs_le_30 : s ≤ 30 := Nat.le_of_dvd (by decide) hs_dvd_30
              interval_cases s <;> (try decide) <;> (exfalso; first | (revert hs_dvd_30; decide) | (revert hs; decide))
            omega
          subst hk_eq_1
          rw [mul_one] at hk
          exact hk
        have hn_eq : n = 4369 := by
          rw [h_eq, hc_eq_257]
        have h_q1_dvd : 535006138814359 ∣ 2^257 - 1 := by
          have h_div_theorem := Nat.div_add_mod (2^257) 535006138814359
          have h_mod : 2^257 % 535006138814359 = 1 := by set_option exponentiation.threshold 1000 in decide
          rw [h_mod] at h_div_theorem
          have h_sub : 2^257 - 1 = 535006138814359 * (2^257 / 535006138814359) := by omega
          rw [h_sub]
          exact dvd_mul_right 535006138814359 (2^257 / 535006138814359)
        have h_257_dvd_n : 257 ∣ n := by
          rw [h_eq, hc_eq_257]
          exact dvd_mul_left 257 17
        have h_257_dvd_mersenne : 2^257 - 1 ∣ 2^n - 1 := Nat.pow_sub_one_dvd_pow_sub_one 2 h_257_dvd_n
        have h_q1_dvd_n : 535006138814359 ∣ 2^n - 1 := dvd_trans h_q1_dvd h_257_dvd_mersenne
        have h_mod_eq : 535006138814359 ≡ 1 [MOD n] := ha 535006138814359 h_q1_dvd_n
        rw [hn_eq] at h_mod_eq
        have h_ge1 : 1 ≤ 535006138814359 := by decide
        have h_mod_eq_symm : 1 ≡ 535006138814359 [MOD 4369] := h_mod_eq.symm
        rw [Nat.modEq_iff_dvd' h_ge1] at h_mod_eq_symm
        have : (535006138814359 - 1) = 535006138814358 := by rfl
        rw [this] at h_mod_eq_symm
        have : 4369 ∣ 535006138814358 := h_mod_eq_symm
        have : 535006138814358 % 4369 = 0 := Nat.mod_eq_zero_of_dvd this
        have : 535006138814358 % 4369 = 2313 := by decide
        omega
    have hp_neq_nineteen : p ≠ 19 := by
      intro h_nineteen
      subst h_nineteen
      have hn_dvd : n ∣ 524286 := by
        have : 2^19 - 2 = 524286 := by rfl
        rw [← this]
        exact h_dvd_sub
      have hc_dvd_27594 : c ∣ 27594 := by
        have h_eq' : n = 19 * c := h_eq
        rw [h_eq'] at hn_dvd
        have h_524286 : 524286 = 19 * 27594 := by rfl
        rw [h_524286] at hn_dvd
        exact (mul_dvd_mul_iff_left (by decide)).mp hn_dvd
      have hc_ge_nineteen : c ≥ 19 := hc_ge_p
      by_cases hc_eq_one : c = 1
      · subst hc_eq_one
        omega
      · obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hc_eq_one
        have hr_dvd_27594 : r ∣ 27594 := dvd_trans hrdvd hc_dvd_27594
        have hr_ge_nineteen : r ≥ 19 := by
          have hr_dvd_n : r ∣ n := by
            rw [h_eq]
            exact dvd_mul_of_dvd_right hrdvd 19
          have hp_eq' : 19 = minFac n := hp_eq
          rw [hp_eq']
          exact Nat.minFac_le_of_dvd hr.two_le hr_dvd_n
        have hr_vals : r = 73 := by
          have h_dvd_mul : r ∣ 378 * 73 := by
            have : 27594 = 378 * 73 := by rfl
            rwa [this] at hr_dvd_27594
          rcases (Nat.Prime.dvd_mul hr).mp h_dvd_mul with hr_dvd_378 | hr_dvd_73
          · have h_dvd_mul' : r ∣ 18 * 21 := by
              have : 378 = 18 * 21 := by rfl
              rwa [this] at hr_dvd_378
            rcases (Nat.Prime.dvd_mul hr).mp h_dvd_mul' with hr_dvd_18 | hr_dvd_21
            · have hr_le_18 : r ≤ 18 := Nat.le_of_dvd (by decide) hr_dvd_18
              have hr_ge_19 : 19 ≤ r := hr_ge_nineteen
              omega
            · have hr_le_21 : r ≤ 21 := Nat.le_of_dvd (by decide) hr_dvd_21
              have hr_ge_19 : 19 ≤ r := hr_ge_nineteen
              interval_cases r <;> (exfalso; first | (revert hr_dvd_21; decide) | (revert hr; decide))
          · have h73 : Nat.Prime 73 := by decide
            have hr_eq : r = 1 ∨ r = 73 := (Nat.dvd_prime h73).mp hr_dvd_73
            rcases hr_eq with rfl | rfl
            · exfalso; exact hr.ne_one rfl
            · rfl
        subst hr_vals
        have hc_eq_73 : c = 73 := by
          obtain ⟨k, hk⟩ := hrdvd
          have hk_dvd_378 : k ∣ 378 := by
            have : 19 * c ∣ 19 * 27594 := by
              rw [← h_eq]
              exact hn_dvd
            rw [hk] at hc_dvd_27594
            have : 73 * k ∣ 73 * 378 := by
              have h_27594 : 27594 = 73 * 378 := by rfl
              rw [h_27594] at hc_dvd_27594
              exact hc_dvd_27594
            exact (mul_dvd_mul_iff_left (by decide)).mp this
          have hk_le_378 : k ≤ 378 := Nat.le_of_dvd (by decide) hk_dvd_378
          have hk_eq_1 : k = 1 := by
            by_contra hk_ne_1
            obtain ⟨s, hs, hsdvd⟩ := Nat.exists_prime_and_dvd hk_ne_1
            have hs_dvd_378 : s ∣ 378 := dvd_trans hsdvd hk_dvd_378
            have hs_ge_19 : s ≥ 19 := by
              have hs_dvd_c : s ∣ c := by
                rw [hk]
                exact dvd_mul_of_dvd_right hsdvd 73
              have hr_dvd_n : s ∣ n := by
                rw [h_eq]
                exact dvd_mul_of_dvd_right hs_dvd_c 19
              have hp_eq' : 19 = minFac n := hp_eq
              rw [hp_eq']
              exact Nat.minFac_le_of_dvd hs.two_le hr_dvd_n
            have hs_le_seven : s ≤ 7 := by
              have h_dvd_mul' : s ∣ 18 * 21 := by
                have : 378 = 18 * 21 := by rfl
                rwa [this] at hs_dvd_378
              rcases (Nat.Prime.dvd_mul hs).mp h_dvd_mul' with hs_dvd_18 | hs_dvd_21
              · have hs_le_18 : s ≤ 18 := Nat.le_of_dvd (by decide) hs_dvd_18
                have hs_ge_19 : s ≥ 19 := hs_ge_19
                omega
              · have hs_le_21 : s ≤ 21 := Nat.le_of_dvd (by decide) hs_dvd_21
                have hs_ge_19 : s ≥ 19 := hs_ge_19
                interval_cases s <;> (exfalso; first | (revert hs_dvd_21; decide) | (revert hs; decide))
            omega
          subst hk_eq_1
          rw [mul_one] at hk
          exact hk
        have hn_eq : n = 1387 := by
          rw [h_eq, hc_eq_73]
        have h_q_dvd : 439 ∣ 2^73 - 1 := by
          have h_div_theorem := Nat.div_add_mod (2^73) 439
          have h_mod : 2^73 % 439 = 1 := by set_option exponentiation.threshold 1000 in decide
          rw [h_mod] at h_div_theorem
          have h_sub : 2^73 - 1 = 439 * (2^73 / 439) := by omega
          rw [h_sub]
          exact dvd_mul_right 439 (2^73 / 439)
        have h_73_dvd_n : 73 ∣ n := by
          rw [h_eq, hc_eq_73]
          exact dvd_mul_left 73 19
        have h_73_dvd_mersenne : 2^73 - 1 ∣ 2^n - 1 := Nat.pow_sub_one_dvd_pow_sub_one 2 h_73_dvd_n
        have h_q_dvd_n : 439 ∣ 2^n - 1 := dvd_trans h_q_dvd h_73_dvd_mersenne
        have h_mod_eq : 439 ≡ 1 [MOD n] := ha 439 h_q_dvd_n
        rw [hn_eq] at h_mod_eq
        have h_ge1 : 1 ≤ 439 := by decide
        have h_mod_eq_symm : 1 ≡ 439 [MOD 1387] := h_mod_eq.symm
        rw [Nat.modEq_iff_dvd' h_ge1] at h_mod_eq_symm
        have : (439 - 1) = 438 := by rfl
        rw [this] at h_mod_eq_symm
        have : 1387 ∣ 438 := h_mod_eq_symm
        have : 1387 ≤ 438 := Nat.le_of_dvd (by decide) this
        omega
    have hp_neq_twenty_three : p ≠ 23 := by
      intro h_twenty_three
      subst h_twenty_three
      have h_q_dvd : 47 ∣ 2^23 - 1 := by
        have h_div_theorem := Nat.div_add_mod (2^23) 47
        have h_mod : 2^23 % 47 = 1 := by decide
        rw [h_mod] at h_div_theorem
        have h_sub : 2^23 - 1 = 47 * (2^23 / 47) := by omega
        rw [h_sub]
        exact dvd_mul_right 47 (2^23 / 47)
      have h_23_dvd_n : 23 ∣ n := by
        rw [h_eq]
        exact dvd_mul_right 23 c
      have h_mersenne_dvd : 2^23 - 1 ∣ 2^n - 1 := Nat.pow_sub_one_dvd_pow_sub_one 2 h_23_dvd_n
      have h_q_dvd_n : 47 ∣ 2^n - 1 := dvd_trans h_q_dvd h_mersenne_dvd
      have h_mod_eq : 47 ≡ 1 [MOD n] := ha 47 h_q_dvd_n
      have h_ge1 : 1 ≤ 47 := by decide
      have h_mod_eq_symm : 1 ≡ 47 [MOD n] := h_mod_eq.symm
      rw [Nat.modEq_iff_dvd' h_ge1] at h_mod_eq_symm
      have : (47 - 1) = 46 := by rfl
      rw [this] at h_mod_eq_symm
      have hn_le : n ≤ 46 := Nat.le_of_dvd (by decide) h_mod_eq_symm
      have hc_ge_23 : c ≥ 23 := hc_ge_p
      have hn_ge : n ≥ 529 := by
        rw [h_eq]
        calc 23 * c ≥ 23 * 23 := Nat.mul_le_mul_left 23 hc_ge_23
        _ = 529 := by decide
      omega
    have hp_neq_twenty_nine : p ≠ 29 := by
      intro h_twenty_nine
      subst h_twenty_nine
      have h_q_dvd : 233 ∣ 2^29 - 1 := by
        have h_div_theorem := Nat.div_add_mod (2^29) 233
        have h_mod : 2^29 % 233 = 1 := by decide
        rw [h_mod] at h_div_theorem
        have h_sub : 2^29 - 1 = 233 * (2^29 / 233) := by omega
        rw [h_sub]
        exact dvd_mul_right 233 (2^29 / 233)
      have h_29_dvd_n : 29 ∣ n := by
        rw [h_eq]
        exact dvd_mul_right 29 c
      have h_mersenne_dvd : 2^29 - 1 ∣ 2^n - 1 := Nat.pow_sub_one_dvd_pow_sub_one 2 h_29_dvd_n
      have h_q_dvd_n : 233 ∣ 2^n - 1 := dvd_trans h_q_dvd h_mersenne_dvd
      have h_mod_eq : 233 ≡ 1 [MOD n] := ha 233 h_q_dvd_n
      have h_ge1 : 1 ≤ 233 := by decide
      have h_mod_eq_symm : 1 ≡ 233 [MOD n] := h_mod_eq.symm
      rw [Nat.modEq_iff_dvd' h_ge1] at h_mod_eq_symm
      have : (233 - 1) = 232 := by rfl
      rw [this] at h_mod_eq_symm
      have hn_le : n ≤ 232 := Nat.le_of_dvd (by decide) h_mod_eq_symm
      have hc_ge_29 : c ≥ 29 := hc_ge_p
      have hn_ge : n ≥ 841 := by
        rw [h_eq]
        calc 29 * c ≥ 29 * 29 := Nat.mul_le_mul_left 29 hc_ge_29
        _ = 841 := by decide
      omega
    have hp_neq_thirty_one : p ≠ 31 := by
      intro h_thirty_one
      subst h_thirty_one
      have hn_dvd : n ∣ 2^31 - 2 := h_dvd_sub
      have hc_dvd : c ∣ (2^31 - 2) / 31 := by
        have h_eq_mul : 2^31 - 2 = 31 * ((2^31 - 2) / 31) := by decide
        rw [h_eq] at hn_dvd
        rw [h_eq_mul] at hn_dvd
        exact (mul_dvd_mul_iff_left (by decide : 31 ≠ 0)).mp hn_dvd
      have hc_val : (2^31 - 2) / 31 = 69273666 := by decide
      rw [hc_val] at hc_dvd
      have h_all_prime_factors : ∀ r, r.Prime → r ∣ c → r ≥ 31 := by
        intro r hr hrdvd
        have hr_dvd_n : r ∣ n := by
          rw [h_eq]
          exact dvd_mul_of_dvd_right hrdvd 31
        have hp_eq' : 31 = minFac n := hp_eq
        rw [hp_eq']
        exact Nat.minFac_le_of_dvd hr.two_le hr_dvd_n
      have hc_ge_two : c ≥ 2 := hc_ge
      obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd (by omega : c ≠ 1)
      have hr_dvd_69273666 : r ∣ 69273666 := dvd_trans hrdvd hc_dvd
      have hr_ge_31 : r ≥ 31 := h_all_prime_factors r hr hrdvd
      have hr_cases : r = 151 ∨ r = 331 := by
        have h_1386 : 1386 = 2 * (3 * (3 * (7 * 11))) := by decide
        have h_mul : 69273666 = 151 * 331 * 1386 := by decide
        rw [h_mul] at hr_dvd_69273666
        rcases (Nat.Prime.dvd_mul hr).mp hr_dvd_69273666 with hr_dvd_151_331 | hr_dvd_1386
        · rcases (Nat.Prime.dvd_mul hr).mp hr_dvd_151_331 with hr_dvd_151 | hr_dvd_331
          · have h151 : Nat.Prime 151 := by set_option maxRecDepth 10000 in decide
            rcases (Nat.dvd_prime h151).mp hr_dvd_151 with rfl | rfl
            · exfalso; exact hr.ne_one rfl
            · exact Or.inl rfl
          · have h331 : Nat.Prime 331 := by set_option maxRecDepth 10000 in decide
            rcases (Nat.dvd_prime h331).mp hr_dvd_331 with rfl | rfl
            · exfalso; exact hr.ne_one rfl
            · exact Or.inr rfl
        · rw [h_1386] at hr_dvd_1386
          rcases (Nat.Prime.dvd_mul hr).mp hr_dvd_1386 with hr_2 | hr_rest1
          · rcases (Nat.dvd_prime Nat.prime_two).mp hr_2 with rfl | rfl
            · exfalso; exact hr.ne_one rfl
            · omega
          · rcases (Nat.Prime.dvd_mul hr).mp hr_rest1 with hr_3 | hr_rest2
            · have h3 : Nat.Prime 3 := by decide
              rcases (Nat.dvd_prime h3).mp hr_3 with rfl | rfl
              · exfalso; exact hr.ne_one rfl
              · omega
            · rcases (Nat.Prime.dvd_mul hr).mp hr_rest2 with hr_3 | hr_rest3
              · have h3 : Nat.Prime 3 := by decide
                rcases (Nat.dvd_prime h3).mp hr_3 with rfl | rfl
                · exfalso; exact hr.ne_one rfl
                · omega
              · rcases (Nat.Prime.dvd_mul hr).mp hr_rest3 with hr_7 | hr_11
                · have h7 : Nat.Prime 7 := by decide
                  rcases (Nat.dvd_prime h7).mp hr_7 with rfl | rfl
                  · exfalso; exact hr.ne_one rfl
                  · omega
                · have h11 : Nat.Prime 11 := by decide
                  rcases (Nat.dvd_prime h11).mp hr_11 with rfl | rfl
                  · exfalso; exact hr.ne_one rfl
                  · omega
      rcases hr_cases with rfl | rfl
      · have h_151_dvd_n : 151 ∣ n := by
          have : 151 ∣ c := hrdvd
          rw [h_eq]
          exact dvd_mul_of_dvd_right this 31
        have h_18121_dvd_mersenne : 18121 ∣ 2^151 - 1 := by
          have h_div_theorem := Nat.div_add_mod (2^151) 18121
          have h_mod : 2^151 % 18121 = 1 := by set_option exponentiation.threshold 1000 in decide
          rw [h_mod] at h_div_theorem
          have h_sub : 2^151 - 1 = 18121 * (2^151 / 18121) := by omega
          rw [h_sub]
          exact dvd_mul_right 18121 (2^151 / 18121)
        have h_151_dvd_mersenne_n : 2^151 - 1 ∣ 2^n - 1 := Nat.pow_sub_one_dvd_pow_sub_one 2 h_151_dvd_n
        have h_18121_dvd_n : 18121 ∣ 2^n - 1 := dvd_trans h_18121_dvd_mersenne h_151_dvd_mersenne_n
        have h_mod_eq : 18121 ≡ 1 [MOD n] := ha 18121 h_18121_dvd_n
        have h_ge1 : 1 ≤ 18121 := by decide
        have h_mod_eq_symm : 1 ≡ 18121 [MOD n] := h_mod_eq.symm
        rw [Nat.modEq_iff_dvd' h_ge1] at h_mod_eq_symm
        have h_4681_dvd_n : 4681 ∣ n := by
          have h_151_dvd_c : 151 ∣ c := hrdvd
          have h_n_eq : n = 31 * c := h_eq
          rw [h_n_eq]
          obtain ⟨k, hk⟩ := h_151_dvd_c
          subst hk
          use k
          ring
        have h_4681_dvd_18120 : 4681 ∣ 18120 := dvd_trans h_4681_dvd_n h_mod_eq_symm
        have h_mod : 18120 % 4681 = 4077 := by decide
        have : ¬ 4681 ∣ 18120 := by
          intro h_dvd
          have h_mod_zero := Nat.mod_eq_zero_of_dvd h_dvd
          omega
        exact this h_4681_dvd_18120
      · have h_331_dvd_n : 331 ∣ n := by
          have : 331 ∣ c := hrdvd
          rw [h_eq]
          exact dvd_mul_of_dvd_right this 31
        have h_16937389168607_dvd_mersenne : 16937389168607 ∣ 2^331 - 1 := by
          have h_div_theorem := Nat.div_add_mod (2^331) 16937389168607
          have h_mod : 2^331 % 16937389168607 = 1 := by set_option exponentiation.threshold 1000 in decide
          rw [h_mod] at h_div_theorem
          have h_sub : 2^331 - 1 = 16937389168607 * (2^331 / 16937389168607) := by omega
          rw [h_sub]
          exact dvd_mul_right 16937389168607 (2^331 / 16937389168607)
        have h_331_dvd_mersenne_n : 2^331 - 1 ∣ 2^n - 1 := Nat.pow_sub_one_dvd_pow_sub_one 2 h_331_dvd_n
        have h_16937389168607_dvd_n : 16937389168607 ∣ 2^n - 1 := dvd_trans h_16937389168607_dvd_mersenne h_331_dvd_mersenne_n
        have h_mod_eq : 16937389168607 ≡ 1 [MOD n] := ha 16937389168607 h_16937389168607_dvd_n
        have h_ge1 : 1 ≤ 16937389168607 := by decide
        have h_mod_eq_symm : 1 ≡ 16937389168607 [MOD n] := h_mod_eq.symm
        rw [Nat.modEq_iff_dvd' h_ge1] at h_mod_eq_symm
        have h_10261_dvd_n : 10261 ∣ n := by
          have h_331_dvd_c : 331 ∣ c := hrdvd
          have h_n_eq : n = 31 * c := h_eq
          rw [h_n_eq]
          obtain ⟨k, hk⟩ := h_331_dvd_c
          subst hk
          use k
          ring
        have h_10261_dvd_big : 10261 ∣ 16937389168606 := dvd_trans h_10261_dvd_n h_mod_eq_symm
        have h_mod : 16937389168606 % 10261 = 331 := by set_option maxRecDepth 100000 in decide
        have : ¬ 10261 ∣ 16937389168606 := by
          intro h_dvd
          have h_mod_zero := Nat.mod_eq_zero_of_dvd h_dvd
          omega
        exact this h_10261_dvd_big
    have hc_lt : c < n := by
      rw [h_eq]
      have : p > 1 := hp.one_lt
      calc c = 1 * c := by ring
      _ < p * c := Nat.mul_lt_mul_of_pos_right this (by omega)
    have hc_gt : c > 1 := hc_ge
    have hac_iff : a c = 2 ↔ c.Prime := ih c hc_lt hc_gt
    have hac : a c = 2 := by
      rw [a_eq_two_iff c hc_gt]
      intro d hdvd
      have hdvd_n : d ∣ 2^n - 1 := by
        have h_pow_dvd : 2^c - 1 ∣ 2^n - 1 := Nat.pow_sub_one_dvd_pow_sub_one 2 hdvd_c
        exact dvd_trans hdvd h_pow_dvd
      have h_mod_n : d ≡ 1 [MOD n] := ha d hdvd_n
      exact Nat.ModEq.of_dvd hdvd_c h_mod_n
    have hc_prime : c.Prime := hac_iff.mp hac
    have hp_cop : Coprime p 2 := by
      have hp_gt_2 : p > 2 := by
        have : p ≠ 2 := hp_neq_two
        have : p ≥ 2 := hp.two_le
        omega
      have : ¬ p ∣ 2 := by
        intro hd
        have : p ≤ 2 := Nat.le_of_dvd (by decide) hd
        omega
      exact hp.coprime_iff_not_dvd.mpr this
    have hc_cop : Coprime c 2 := by
      have hc_gt_2 : c > 2 := by
        have : c ≥ p := hc_ge_p
        have : p > 2 := by
          have : p ≠ 2 := hp_neq_two
          have : p ≥ 2 := hp.two_le
          omega
        omega
      have : ¬ c ∣ 2 := by
        intro hd
        have : c ≤ 2 := Nat.le_of_dvd (by decide) hd
        omega
      exact hc_prime.coprime_iff_not_dvd.mpr this
    have hp_cop_2 : Coprime 2 p := hp_cop.symm
    have hc_cop_2 : Coprime 2 c := hc_cop.symm
    have hp_fermat : 2^(p-1) ≡ 1 [MOD p] := Nat.ModEq.pow_card_sub_one_eq_one hp hp_cop_2
    have hp_dvd_fermat : p ∣ 2^(p-1) - 1 := by
      have : 1 ≤ 2^(p-1) := Nat.one_le_pow (p-1) 2 (by decide)
      exact (Nat.modEq_iff_dvd' this).mp hp_fermat.symm
    have hc_fermat : 2^(c-1) ≡ 1 [MOD c] := Nat.ModEq.pow_card_sub_one_eq_one hc_prime hc_cop_2
    have hc_dvd_fermat : c ∣ 2^(c-1) - 1 := by
      have : 1 ≤ 2^(c-1) := Nat.one_le_pow (c-1) 2 (by decide)
      exact (Nat.modEq_iff_dvd' this).mp hc_fermat.symm
    have hc_dvd_p_sub : c ∣ 2^(p-1) - 1 := by
      have h_n_dvd : n ∣ 2 * (2^(p-1) - 1) := by
        have h_pow_sub : 2^p = 2 * 2^(p-1) := by
          have h_ge2 : p ≥ 2 := hp.two_le
          have h_eq' : p = p - 1 + 1 := by omega
          nth_rw 1 [h_eq']
          rw [pow_succ, mul_comm]
        have h_sub_eq : 2^p - 2 = 2 * (2^(p-1) - 1) := by
          rw [h_pow_sub]
          have : 2^(p-1) ≥ 1 := Nat.one_le_pow (p - 1) 2 (by decide)
          omega
        rw [← h_sub_eq]
        exact h_dvd_sub
      have hc_dvd_mul : c ∣ 2 * (2^(p-1) - 1) := dvd_trans hdvd_c h_n_dvd
      exact hc_cop.dvd_of_dvd_mul_left hc_dvd_mul
    have hp_dvd_c_sub : p ∣ 2^(c-1) - 1 := by
      have h_all_prime_factors : ∀ v, v.Prime → v ∣ 2^c - 1 → v ≡ 1 [MOD p] := by
        intro v hv hvdvd
        have hvdvd_n : v ∣ 2^n - 1 := by
          have h_pow_dvd : 2^c - 1 ∣ 2^n - 1 := Nat.pow_sub_one_dvd_pow_sub_one 2 hdvd_c
          exact dvd_trans hvdvd h_pow_dvd
        have h_mod_n : v ≡ 1 [MOD n] := ha v hvdvd_n
        have hp_dvd_n : p ∣ n := by
          rw [h_eq]
          exact dvd_mul_right p c
        exact Nat.ModEq.of_dvd hp_dvd_n h_mod_n
      have h_pow_gt : 2^c - 1 > 0 := by
        have : 2^c ≥ 2^2 := Nat.pow_le_pow_right (by decide) hc_ge
        omega
      have h_mod_p : 2^c - 1 ≡ 1 [MOD p] := modEq_one_of_prime_factors p (2^c - 1) h_pow_gt h_all_prime_factors
      have hp_dvd_sub_one : p ∣ (2^c - 1) - 1 := by
        have h_ge1 : 1 ≤ 2^c - 1 := by
          have : 2^c ≥ 2^2 := Nat.pow_le_pow_right (by decide) hc_ge
          omega
        have h_mod_p_symm : 1 ≡ 2^c - 1 [MOD p] := h_mod_p.symm
        exact (Nat.modEq_iff_dvd' h_ge1).mp h_mod_p_symm
      have h_pow_sub_eq : (2^c - 1) - 1 = 2 * (2^(c-1) - 1) := by
        have h_pow_sub : 2^c = 2 * 2^(c-1) := by
          have h_ge2 : c ≥ 2 := hc_prime.two_le
          have h_eq' : c = c - 1 + 1 := by omega
          nth_rw 1 [h_eq']
          rw [pow_succ, mul_comm]
        rw [h_pow_sub]
        have : 2^(c-1) ≥ 1 := Nat.one_le_pow (c - 1) 2 (by decide)
        omega
      rw [h_pow_sub_eq] at hp_dvd_sub_one
      exact hp_cop.dvd_of_dvd_mul_left hp_dvd_sub_one
    let g := Nat.gcd (p-1) (c-1)
    have hc_dvd_gcd_mersenne : c ∣ 2^g - 1 := by
      have h_gcd_eq : Nat.gcd (2^(p-1) - 1) (2^(c-1) - 1) = 2^g - 1 := Nat.pow_sub_one_gcd_pow_sub_one 2 (p-1) (c-1)
      have h_dvd_gcd : c ∣ Nat.gcd (2^(p-1) - 1) (2^(c-1) - 1) := Nat.dvd_gcd hc_dvd_p_sub hc_dvd_fermat
      rwa [h_gcd_eq] at h_dvd_gcd
    have hp_dvd_gcd_mersenne : p ∣ 2^g - 1 := by
      have h_gcd_eq : Nat.gcd (2^(p-1) - 1) (2^(c-1) - 1) = 2^g - 1 := Nat.pow_sub_one_gcd_pow_sub_one 2 (p-1) (c-1)
      have h_dvd_gcd : p ∣ Nat.gcd (2^(p-1) - 1) (2^(c-1) - 1) := Nat.dvd_gcd hp_dvd_fermat hp_dvd_c_sub
      rwa [h_gcd_eq] at h_dvd_gcd
    have hdvd_p : p ∣ n := by
      rw [h_eq]
      exact dvd_mul_right p c
    have hn_dvd_p_sub : n ∣ 2^(p-1) - 1 := by
      have h_all_prime_factors : ∀ v, v.Prime → v ∣ 2^p - 1 → v ≡ 1 [MOD n] := by
        intro v hv hvdvd
        have hvdvd_n : v ∣ 2^n - 1 := by
          have h_pow_dvd : 2^p - 1 ∣ 2^n - 1 := Nat.pow_sub_one_dvd_pow_sub_one 2 hdvd_p
          exact dvd_trans hvdvd h_pow_dvd
        exact ha v hvdvd_n
      have h_pow_gt : 2^p - 1 > 0 := by
        have : 2^p ≥ 2^2 := Nat.pow_le_pow_right (by decide) hp.two_le
        omega
      have h_mod_n : 2^p - 1 ≡ 1 [MOD n] := modEq_one_of_prime_factors n (2^p - 1) h_pow_gt h_all_prime_factors
      have hn_dvd_sub_one : n ∣ (2^p - 1) - 1 := by
        have h_ge1 : 1 ≤ 2^p - 1 := by
          have : 2^p ≥ 2^2 := Nat.pow_le_pow_right (by decide) hp.two_le
          omega
        have h_mod_n_symm : 1 ≡ 2^p - 1 [MOD n] := h_mod_n.symm
        exact (Nat.modEq_iff_dvd' h_ge1).mp h_mod_n_symm
      have h_pow_sub_eq : (2^p - 1) - 1 = 2 * (2^(p-1) - 1) := by
        have h_pow_sub : 2^p = 2 * 2^(p-1) := by
          have h_ge2 : p ≥ 2 := hp.two_le
          have h_eq' : p = p - 1 + 1 := by omega
          nth_rw 1 [h_eq']
          rw [pow_succ, mul_comm]
        rw [h_pow_sub]
        have : 2^(p-1) ≥ 1 := Nat.one_le_pow (p - 1) 2 (by decide)
        omega
      rw [h_pow_sub_eq] at hn_dvd_sub_one
      have hn_cop : Coprime n 2 := by
        rw [h_eq]
        exact Coprime.mul_left hp_cop hc_cop
      exact hn_cop.dvd_of_dvd_mul_left hn_dvd_sub_one
    have h_pc_dvd_gcd_mersenne : p * c ∣ 2^g - 1 := by
      by_cases h_pc : p = c
      · subst h_pc
        have h_g : g = p - 1 := by
          dsimp [g]
          exact Nat.gcd_self (p-1)
        rw [h_g]
        rw [← h_eq]
        exact hn_dvd_p_sub
      · have hp_lt_c : p < c := by
          have : c ≥ p := hc_ge_p
          omega
        have h_cop_pc : Coprime p c := by
          have : ¬ p ∣ c := by
            intro hd
            have : c = p := (Nat.Prime.dvd_iff_eq hc_prime hp.ne_one).mp hd
            exact h_pc this.symm
          exact hp.coprime_iff_not_dvd.mpr this
        exact h_cop_pc.mul_dvd_of_dvd_of_dvd hp_dvd_gcd_mersenne hc_dvd_gcd_mersenne
    by_cases hg : g = p - 1
    · sorry
    ·
        have hp_ge2 : p ≥ 2 := hp.two_le
        have h_g_le_p : g ≤ p - 1 := Nat.gcd_le_left (c - 1) (by omega : 0 < p - 1)
        have h_g_lt : g < p - 1 := by omega
        have h_g_le : g ≤ (p - 1) / 2 := by
          have h_div : g ∣ p - 1 := Nat.gcd_dvd_left (p-1) (c-1)
          obtain ⟨k, hk⟩ := h_div
          have : k ≥ 2 := by
            by_contra hk_le
            have : k ≤ 1 := by omega
            interval_cases k
            · rw [mul_zero] at hk; omega
            · rw [mul_one] at hk; omega
          rw [hk]
          have h_le2 : g * k / 2 ≥ g * 2 / 2 := Nat.div_le_div_right (Nat.mul_le_mul_left g this)
          have h_cancel : g * 2 / 2 = g := Nat.mul_div_cancel g (by decide : 2 > 0)
          omega
        have h_g_pos : g > 0 := Nat.gcd_pos_of_pos_left (c - 1) (by omega : p - 1 > 0)
        have h_mersenne_pos : 2^g - 1 > 0 := by
          have : 2^g ≥ 2^1 := Nat.pow_le_pow_right (by decide) h_g_pos
          omega
        have h_pc_le_mersenne : p * c ≤ 2^g - 1 := Nat.le_of_dvd h_mersenne_pos h_pc_dvd_gcd_mersenne
        have h_mersenne_le : 2^g - 1 ≤ 2^((p-1)/2) - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide) h_g_le) 1
        have h_pc_le_half : p * c ≤ 2^((p-1)/2) - 1 := le_trans h_pc_le_mersenne h_mersenne_le
        have h_pc_cop : Coprime (p * c) 2 := by
          have : Coprime p 2 := hp_cop
          have : Coprime c 2 := hc_cop
          exact Coprime.mul_left (by assumption) (by assumption)
        have h_pc_dvd_sub_one : p * c ∣ 2^(p-1) - 1 := by
          have h_n_dvd : n ∣ 2 * (2^(p-1) - 1) := by
            have h_pow_sub : 2^p = 2 * 2^(p-1) := by
              have h_ge2 : p ≥ 2 := hp.two_le
              have h_eq' : p = p - 1 + 1 := by omega
              nth_rw 1 [h_eq']
              rw [pow_succ, mul_comm]
            have h_sub_eq : 2^p - 2 = 2 * (2^(p-1) - 1) := by
              rw [h_pow_sub]
              have : 2^(p-1) ≥ 1 := Nat.one_le_pow (p - 1) 2 (by decide)
              omega
            rw [← h_sub_eq]
            exact h_dvd_sub
          rw [h_eq] at h_n_dvd
          exact h_pc_cop.dvd_of_dvd_mul_left h_n_dvd
        obtain ⟨j, hj⟩ := h_pc_dvd_sub_one
        have hj_pos : j > 0 := by
          have h_pow_pos : 2^(p-1) - 1 > 0 := by
            have h_ge1 : p - 1 ≥ 1 := by omega
            have : 2^(p-1) ≥ 2^1 := Nat.pow_le_pow_right (by decide) h_ge1
            omega
          by_contra hj0
          have : j = 0 := by omega
          subst this
          rw [mul_zero] at hj
          omega
        have h_diff_squares : 2^(p-1) - 1 = (2^((p-1)/2) - 1) * (2^((p-1)/2) + 1) := by
          have h_eq2 : p - 1 = (p - 1) / 2 + (p - 1) / 2 := by
            have h_odd : Odd p := Nat.odd_iff.mpr (hp.eq_two_or_odd.resolve_left hp_neq_two)
            obtain ⟨k, hk⟩ := h_odd
            omega
          nth_rw 1 [h_eq2]
          rw [pow_add]
          have h_le : 1 ≤ 2 ^ ((p - 1) / 2) := Nat.one_le_pow _ 2 (by decide)
          rw [Nat.sub_mul, Nat.mul_add, one_mul, mul_one]
          omega
        have hj_ge : j ≥ 2^((p-1)/2) + 1 := by
          by_contra hj_lt
          have : j ≤ 2^((p-1)/2) := by omega
          have h1 : j * p * c ≤ 2^((p-1)/2) * (2^((p-1)/2) - 1) := by
            have h_step1 : j * p * c ≤ 2^((p-1)/2) * p * c := by
              have : j * (p * c) ≤ 2^((p-1)/2) * (p * c) := Nat.mul_le_mul_right (p * c) this
              rwa [← mul_assoc, ← mul_assoc] at this
            have h_step2 : 2^((p-1)/2) * p * c ≤ 2^((p-1)/2) * (2^((p-1)/2) - 1) := by
              have : 2^((p-1)/2) * (p * c) ≤ 2^((p-1)/2) * (2^((p-1)/2) - 1) := Nat.mul_le_mul_left _ h_pc_le_half
              rwa [← mul_assoc] at this
            exact le_trans h_step1 h_step2
          have h2 : 2^((p-1)/2) * (2^((p-1)/2) - 1) < (2^((p-1)/2) - 1) * (2^((p-1)/2) + 1) := by
            have h_ge18 : (p-1)/2 ≥ 18 := by
              -- since p >= 37
              -- we can prove p >= 37 from hp_neq_two ... hp_neq_thirty_one
              have : p ≥ 37 := by
                by_contra h_lt
                have h_lt' : p < 37 := by omega
                have hp_ge : p ≥ 2 := hp.two_le
                interval_cases p
                · exact hp_neq_two rfl
                · exact hp_neq_three rfl
                · revert hp; decide
                · exact hp_neq_five rfl
                · revert hp; decide
                · exact hp_neq_seven rfl
                · revert hp; decide
                · revert hp; decide
                · revert hp; decide
                · exact hp_neq_eleven rfl
                · revert hp; decide
                · exact hp_neq_thirteen rfl
                · revert hp; decide
                · revert hp; decide
                · revert hp; decide
                · exact hp_neq_seventeen rfl
                · revert hp; decide
                · exact hp_neq_nineteen rfl
                · revert hp; decide
                · revert hp; decide
                · revert hp; decide
                · exact hp_neq_twenty_three rfl
                · revert hp; decide
                · revert hp; decide
                · revert hp; decide
                · revert hp; decide
                · revert hp; decide
                · exact hp_neq_twenty_nine rfl
                · revert hp; decide
                · exact hp_neq_thirty_one rfl
                · revert hp; decide
                · revert hp; decide
                · revert hp; decide
                · revert hp; decide
                · revert hp; decide
              omega
            have h_ge2 : 2^((p-1)/2) ≥ 2 := by
              have : 2^((p-1)/2) ≥ 2^18 := Nat.pow_le_pow_right (by decide) h_ge18
              omega
            rw [mul_comm (2^((p-1)/2))]
            rw [Nat.mul_add, mul_one]
            omega
          have h_jpc : j * p * c = (2^((p-1)/2) - 1) * (2^((p-1)/2) + 1) := by
            have : j * p * c = p * c * j := by ring
            rw [this, ← hj, h_diff_squares]
          rw [h_jpc] at h1
          exact (Nat.lt_le_asymm h2 h1).elim
  · intro hp
    exact a_eq_two_of_prime n h_n hp
