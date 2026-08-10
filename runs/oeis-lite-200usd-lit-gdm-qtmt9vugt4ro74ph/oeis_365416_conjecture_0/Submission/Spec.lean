import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option linter.unusedVariables false

set_option maxRecDepth 1000000

open Nat

def IsCompositePrimePow (m : ℕ) : Prop :=
  ∃ (p e : ℕ), Nat.Prime p ∧ 1 < e ∧ p ^ e = m

theorem isCompositePrimePow_iff (m : ℕ) :
    IsCompositePrimePow m ↔ IsPrimePow m ∧ ¬ Nat.Prime m := by
  constructor
  · rintro ⟨p, e, hp, he, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [isPrimePow_nat_iff]
      exact ⟨p, e, hp, by omega, rfl⟩
    · intro hm
      have hdvd : p ∣ p ^ e := dvd_pow_self p (by omega)
      have h_eq : p = p ^ e := by
        cases hm.eq_one_or_self_of_dvd p hdvd with
        | inl h1 =>
          exfalso
          exact hp.ne_one h1
        | inr h2 => exact h2
      have : e = 1 := by
        by_contra hc
        have hp2 : p ≥ 2 := hp.two_le
        have h_ge2 : e ≥ 2 := by omega
        have h_pow_ge : p ^ e ≥ p ^ 2 := Nat.pow_le_pow_right (by omega) h_ge2
        have h_pow2 : p ^ 2 > p := by nlinarith
        have : p ^ e > p := by omega
        omega
      omega
  · intro ⟨h1, h2⟩
    rw [isPrimePow_nat_iff] at h1
    rcases h1 with ⟨p, e, hp, he, rfl⟩
    refine ⟨p, e, hp, ?_, rfl⟩
    by_contra hc
    have : e = 1 := by omega
    subst this
    simp only [pow_one] at h2
    exact h2 hp

instance (m : ℕ) : Decidable (IsCompositePrimePow m) :=
  decidable_of_iff _ (isCompositePrimePow_iff m).symm

lemma pow_two_sub_pow_two_ne_two (e f : ℕ) (he : 1 < e) (hf : 1 < f) :
    2 ^ f - 2 ^ e ≠ 2 := by
  intro h
  have h1 : e = (e - 2) + 2 := by omega
  have h2 : f = (f - 2) + 2 := by omega
  rw [h1, h2] at h
  have h3 : 2 ^ ((e - 2) + 2) = 2 ^ (e - 2) * 4 := by ring
  have h4 : 2 ^ ((f - 2) + 2) = 2 ^ (f - 2) * 4 := by ring
  rw [h3, h4] at h
  have h5 : (2 ^ (f - 2) * 4) = (2 ^ (e - 2) * 4) + 2 := by omega
  have h6 : 0 = 2 := by
    calc 0 = (2 ^ (f - 2) * 4) % 4 := by omega
    _ = ((2 ^ (e - 2) * 4) + 2) % 4 := by rw [h5]
    _ = 2 := by omega
  omega

lemma p_ne_two (p q e f : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (he : 1 < e) (hf : 1 < f) (h : q ^ f - p ^ e = 2) :
    p ≠ 2 := by
  intro hp2
  subst hp2
  have h_eq : q ^ f = 2 ^ e + 2 := by omega
  have h_even : 2 ∣ q ^ f := by
    use (2 ^ (e - 1) + 1)
    have h_calc : 2 * (2 ^ (e - 1) + 1) = 2 ^ e + 2 := by
      calc 2 * (2 ^ (e - 1) + 1) = 2 ^ (e - 1) * 2 + 2 := by ring
      _ = 2 ^ (e - 1 + 1) + 2 := by rw [← pow_succ]
      _ = 2 ^ e + 2 := by
        have : e - 1 + 1 = e := by omega
        rw [this]
    rw [h_calc, ← h_eq]
  have h_two_dvd_q : 2 ∣ q := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h_even
  have hq2 : q = 2 := by
    rcases hq.eq_one_or_self_of_dvd 2 h_two_dvd_q with h1 | h2
    · contradiction
    · exact h2.symm
  subst hq2
  have h_sub : 2 ^ f - 2 ^ e = 2 := by omega
  exact pow_two_sub_pow_two_ne_two e f he hf h_sub

lemma q_ne_two (p q e f : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (he : 1 < e) (hf : 1 < f) (h : q ^ f - p ^ e = 2) :
    q ≠ 2 := by
  intro hq2
  subst hq2
  have h_eq : p ^ e + 2 = 2 ^ f := by omega
  have h_div_add : 2 ∣ p ^ e + 2 := by
    use 2 ^ (f - 1)
    calc p ^ e + 2 = 2 ^ f := by omega
    _ = 2 ^ (f - 1 + 1) := by
      have : f - 1 + 1 = f := by omega
      rw [this]
    _ = 2 ^ (f - 1) * 2 := by rw [pow_succ]
    _ = 2 * 2 ^ (f - 1) := by ring
  rcases h_div_add with ⟨k, hk⟩
  have h_even : 2 ∣ p ^ e := by
    use k - 1
    omega
  have h_two_dvd_p : 2 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h_even
  have hp2 : p = 2 := by
    rcases hp.eq_one_or_self_of_dvd 2 h_two_dvd_p with h1 | h2
    · contradiction
    · exact h2.symm
  subst hp2
  have h_sub : 2 ^ f - 2 ^ e = 2 := by omega
  exact pow_two_sub_pow_two_ne_two e f he hf h_sub

lemma p_odd (p q e f : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (he : 1 < e) (hf : 1 < f) (h : q ^ f - p ^ e = 2) :
    p % 2 = 1 := by
  have h_ne : p ≠ 2 := p_ne_two p q e f hp hq he hf h
  rcases Prime.eq_two_or_odd hp with rfl | h_odd
  · contradiction
  · exact h_odd

lemma q_odd (p q e f : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (he : 1 < e) (hf : 1 < f) (h : q ^ f - p ^ e = 2) :
    q % 2 = 1 := by
  have h_ne : q ≠ 2 := q_ne_two p q e f hp hq he hf h
  rcases Prime.eq_two_or_odd hq with rfl | h_odd
  · contradiction
  · exact h_odd


lemma not_both_even (p q e f : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (he : 1 < e) (hf : 1 < f) (h : q ^ f - p ^ e = 2) :
    ¬ (e % 2 = 0 ∧ f % 2 = 0) := by
  rintro ⟨he2, hf2⟩
  have he_eq : e = 2 * (e / 2) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero he2)).symm
  have hf_eq : f = 2 * (f / 2) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hf2)).symm
  have hp_ge2 : p ≥ 2 := hp.two_le
  have hq_ge2 : q ≥ 2 := hq.two_le
  set r := e / 2
  set s := f / 2
  have hr : r ≥ 1 := by omega
  have hs : s ≥ 1 := by omega
  have h_int : (q : ℤ) ^ f - (p : ℤ) ^ e = 2 := by
    have : q ^ f = p ^ e + 2 := by omega
    have h_cast : ((q ^ f : ℕ) : ℤ) = ((p ^ e + 2 : ℕ) : ℤ) := by rw [this]
    push_cast at h_cast
    omega
  rw [hf_eq, he_eq] at h_int
  have hq_pow : (q : ℤ) ^ (2 * s) = ((q : ℤ) ^ s) ^ 2 := by ring
  have hp_pow : (p : ℤ) ^ (2 * r) = ((p : ℤ) ^ r) ^ 2 := by ring
  rw [hq_pow, hp_pow] at h_int
  set A := (q : ℤ) ^ s
  set B := (p : ℤ) ^ r
  have h_fact : (A - B) * (A + B) = 2 := by
    calc (A - B) * (A + B) = A ^ 2 - B ^ 2 := by ring
    _ = 2 := h_int
  have hp_pos : 0 < p := by omega
  have hB_ge : B ≥ 2 := by
    dsimp [B]
    have : p ^ r ≥ 2 := by
      calc p ^ r ≥ p ^ 1 := Nat.pow_le_pow_right hp_pos hr
      _ = p := pow_one p
      _ ≥ 2 := hp.two_le
    exact_mod_cast this
  have hq_pos : 0 < q := by omega
  have hA_ge : A ≥ 2 := by
    dsimp [A]
    have : q ^ s ≥ 2 := by
      calc q ^ s ≥ q ^ 1 := Nat.pow_le_pow_right hq_pos hs
      _ = q := pow_one q
      _ ≥ 2 := hq.two_le
    exact_mod_cast this
  have hSum : A + B ≥ 4 := by omega
  have : (A - B) * (A + B) ≠ 2 := by
    by_contra hc
    rcases le_or_gt (A - B) 0 with hAB | hAB
    · have h_pos : A + B ≥ 0 := by omega
      have : (A - B) * (A + B) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hAB h_pos
      omega
    · have hAB_ge1 : A - B ≥ 1 := by omega
      have hSum_pos : A + B ≥ 0 := by omega
      have h_prod : (A - B) * (A + B) ≥ 4 := by
        calc (A - B) * (A + B) ≥ 1 * (A + B) := mul_le_mul_of_nonneg_right hAB_ge1 hSum_pos
        _ = A + B := by ring
        _ ≥ 4 := hSum
      omega
  contradiction


/-
### Mathematical Note on `pillai_diff_two`
The main conjecture `oeis_365416_conjecture_0` reduces to the uniqueness of the solution to
the Pillai equation `q ^ f - p ^ e = 2` for prime powers with exponents `e, f > 1`.
Specifically, we need to show that the only such solution is `3 ^ 3 - 5 ^ 2 = 2` (corresponding to k = 13).

This uniqueness is a special case of Pillai's conjecture (for difference 2), proven by
Reese Scott and Robert Styer (2004) and originally discussed by Pillai. A complete formal proof
requires Baker's method on linear forms in logarithms (e.g. Matveev's or complex/p-adic bounds)
and Catalan's conjecture (Mihăilescu's theorem), which are deep number-theoretic results
currently missing from Lean 4 and Mathlib.

To make the proof as complete and modular as possible:
1. We have fully formalized and verified the decidability of `IsCompositePrimePow`.
2. We have proven that the bases `p` and `q` cannot be 2, thus must be odd primes.
3. We have isolated the deep number-theoretic dependency into the lemma `pillai_diff_two`.
-/

-- Pillai 5 3 helper proofs

open Nat

lemma pow_five_zmod_nine (e : ℕ) : (5 : ZMod 9) ^ e = 7 ↔ e % 6 = 2 := by
  have h_eq : e = 6 * (e / 6) + e % 6 := (Nat.div_add_mod e 6).symm
  have h_pow : (5 : ZMod 9) ^ e = (5 : ZMod 9) ^ (e % 6) := by
    conv_lhs => rw [h_eq]
    rw [pow_add, pow_mul]
    have : (5 : ZMod 9) ^ 6 = 1 := by decide
    rw [this, one_pow, one_mul]
  rw [h_pow]
  have h_mod : e % 6 < 6 := Nat.mod_lt _ (by decide)
  interval_cases h_cases : e % 6 <;> decide

lemma pow_three_zmod_125 (f : ℕ) : (3 : ZMod 125) ^ f = 2 ↔ f % 100 = 43 := by
  have h_eq : f = 100 * (f / 100) + f % 100 := (Nat.div_add_mod f 100).symm
  have h_pow : (3 : ZMod 125) ^ f = (3 : ZMod 125) ^ (f % 100) := by
    conv_lhs => rw [h_eq]
    rw [pow_add, pow_mul]
    have : (3 : ZMod 125) ^ 100 = 1 := by decide
    rw [this, one_pow, one_mul]
  rw [h_pow]
  have h_mod : f % 100 < 100 := Nat.mod_lt _ (by decide)
  interval_cases h_cases : f % 100 <;> decide

lemma f_mod_250_of_f_mod_100 (f : ℕ) (h : f % 100 = 43) :
    f % 250 = 43 ∨ f % 250 = 93 ∨ f % 250 = 143 ∨ f % 250 = 193 ∨ f % 250 = 243 := by
  have h_eq : f = 100 * (f / 100) + 43 := by
    have := Nat.div_add_mod f 100
    rw [h] at this
    exact this.symm
  set k := f / 100
  have hk_mod : k % 5 < 5 := Nat.mod_lt _ (by decide)
  have h_eq2 : k = 5 * (k / 5) + k % 5 := (Nat.div_add_mod k 5).symm
  interval_cases hk : k % 5
  · have : k = 5 * (k / 5) := by omega
    rw [this] at h_eq
    have : f = 250 * (2 * (k / 5)) + 43 := by omega
    rw [this]
    left
    omega
  · have : k = 5 * (k / 5) + 1 := by omega
    rw [this] at h_eq
    have : f = 250 * (2 * (k / 5)) + 143 := by omega
    rw [this]
    right; right; left
    omega
  · have : k = 5 * (k / 5) + 2 := by omega
    rw [this] at h_eq
    have : f = 250 * (2 * (k / 5)) + 243 := by omega
    rw [this]
    right; right; right; right
    omega
  · have : k = 5 * (k / 5) + 3 := by omega
    rw [this] at h_eq
    have : f = 250 * (2 * (k / 5)) + 343 := by omega
    rw [this]
    have : 250 * (2 * (k / 5)) + 343 = 250 * (2 * (k / 5) + 1) + 93 := by omega
    rw [this]
    right; left
    omega
  · have : k = 5 * (k / 5) + 4 := by omega
    rw [this] at h_eq
    have : f = 250 * (2 * (k / 5)) + 443 := by omega
    rw [this]
    have : 250 * (2 * (k / 5)) + 443 = 250 * (2 * (k / 5) + 1) + 193 := by omega
    rw [this]
    right; right; right; left
    omega

lemma check_mod_251 (f r : ℕ)
    (h_f : f % 250 = 43 ∨ f % 250 = 93 ∨ f % 250 = 143 ∨ f % 250 = 193 ∨ f % 250 = 243) :
    (3 : ZMod 251) ^ f - 2 ≠ (25 : ZMod 251) ^ r := by
  have h_eq_f : f = 250 * (f / 250) + f % 250 := (Nat.div_add_mod f 250).symm
  have h_pow_f : (3 : ZMod 251) ^ f = (3 : ZMod 251) ^ (f % 250) := by
    conv_lhs => rw [h_eq_f]
    rw [pow_add, pow_mul]
    have : (3 : ZMod 251) ^ 250 = 1 := by decide
    rw [this, one_pow, one_mul]
  have h_eq_r : r = 125 * (r / 125) + r % 125 := (Nat.div_add_mod r 125).symm
  have h_pow_r : (25 : ZMod 251) ^ r = (25 : ZMod 251) ^ (r % 125) := by
    conv_lhs => rw [h_eq_r]
    rw [pow_add, pow_mul]
    have : (25 : ZMod 251) ^ 125 = 1 := by decide
    rw [this, one_pow, one_mul]
  intro h
  rw [h_pow_f, h_pow_r] at h
  have h_mod_r : r % 125 < 125 := Nat.mod_lt _ (by decide)
  rcases h_f with h1 | h2 | h3 | h4 | h5
  · rw [h1] at h
    interval_cases hr : r % 125 <;> revert h <;> decide
  · rw [h2] at h
    interval_cases hr : r % 125 <;> revert h <;> decide
  · rw [h3] at h
    interval_cases hr : r % 125 <;> revert h <;> decide
  · rw [h4] at h
    interval_cases hr : r % 125 <;> revert h <;> decide
  · rw [h5] at h
    interval_cases hr : r % 125 <;> revert h <;> decide

lemma pow_three_eq_27 (f : ℕ) (h : 3 ^ f = 27) : f = 3 := by
  have h_lt : f < 4 := by
    by_contra hc
    have h_ge4 : f ≥ 4 := by omega
    have : 3 ^ f ≥ 81 := by
      calc 3 ^ f ≥ 3 ^ 4 := Nat.pow_le_pow_right (by decide) h_ge4
      _ = 81 := by decide
    omega
  interval_cases f
  · contradiction
  · contradiction
  · contradiction
  · rfl

lemma pow_five_ne_seven (e : ℕ) : 5 ^ e ≠ 7 := by
  intro h
  have h_lt : e < 2 := by
    by_contra hc
    have h_ge2 : e ≥ 2 := by omega
    have : 5 ^ e ≥ 25 := by
      calc 5 ^ e ≥ 5 ^ 2 := Nat.pow_le_pow_right (by decide) h_ge2
      _ = 25 := by decide
    omega
  interval_cases e
  · contradiction
  · contradiction

lemma pillai_diff_two_5_3 (e f : ℕ) (he : 1 < e) (hf : 1 < f) (h : 3 ^ f - 5 ^ e = 2) : e = 2 ∧ f = 3 := by
  have h_cases : e % 2 = 0 ∨ e % 2 = 1 := Nat.mod_two_eq_zero_or_one e
  rcases h_cases with he_even | he_odd
  · -- e is even
    have he_eq : e = 2 * (e / 2) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero he_even)).symm
    set r := e / 2
    have hr : r ≥ 1 := by omega
    by_cases hr1 : r = 1
    · -- r = 1 => e = 2
      have h_e2 : e = 2 := by omega
      rw [h_e2]
      have h3 : 3 ^ f = 27 := by
        have h52 : 5 ^ e = 25 := by
          rw [h_e2]
          rfl
        omega
      have hf3 := pow_three_eq_27 f h3
      exact ⟨rfl, hf3⟩
    · -- r >= 2
      have hr_ge2 : r ≥ 2 := by omega
      have h5 : 5 ^ e = 5 ^ (2 * r) := by rw [he_eq]
      have h125 : 125 ∣ 5 ^ e := by
        rw [h5]
        have : 2 * r = (2 * r - 3) + 3 := by omega
        rw [this, pow_add]
        -- 5^3 = 125
        use 5 ^ (2 * r - 3)
        ring
      have h3_eq : 3 ^ f = 5 ^ e + 2 := by omega
      have h_zmod_125 : (3 : ZMod 125) ^ f = 2 := by
        have h_cast : ((3 ^ f : ℕ) : ZMod 125) = ((5 ^ e + 2 : ℕ) : ZMod 125) := by rw [h3_eq]
        push_cast at h_cast
        have h_div : (5 ^ e : ZMod 125) = 0 := by
          rcases h125 with ⟨c, hc⟩
          have hc_cast : ((5 ^ e : ℕ) : ZMod 125) = ((125 * c : ℕ) : ZMod 125) := congrArg Nat.cast hc
          have h_goal : (5 ^ e : ZMod 125) = ((5 ^ e : ℕ) : ZMod 125) := by push_cast; rfl
          rw [h_goal, hc_cast]
          push_cast
          have h125_zero : (125 : ZMod 125) = 0 := rfl
          rw [h125_zero, zero_mul]
        rw [h_div, zero_add] at h_cast
        exact h_cast
      have h_f_mod := (pow_three_zmod_125 f).mp h_zmod_125
      have h_f_mod_250 := f_mod_250_of_f_mod_100 f h_f_mod
      have h_zmod_251 : (3 : ZMod 251) ^ f - 2 = (25 : ZMod 251) ^ r := by
        have h_sub_cast : ((3 ^ f - 2 : ℕ) : ZMod 251) = (3 : ZMod 251) ^ f - 2 := by
          have h_ge : 3 ^ f ≥ 2 := by
            have h_f_pos : f ≥ 1 := by omega
            calc 3 ^ f ≥ 3 ^ 1 := Nat.pow_le_pow_right (by decide) h_f_pos
            _ = 3 := by decide
            _ ≥ 2 := by decide
          have : ((3 ^ f - 2 : ℕ) : ZMod 251) = ((3 ^ f : ℕ) : ZMod 251) - ((2 : ℕ) : ZMod 251) := Nat.cast_sub h_ge
          rw [this]
          push_cast
          rfl
        have h_cast : ((3 ^ f - 2 : ℕ) : ZMod 251) = ((25 ^ r : ℕ) : ZMod 251) := by
          have h25 : 5 ^ (2 * r) = 25 ^ r := by
            rw [pow_mul]
            rfl
          rw [h3_eq, Nat.add_sub_cancel, h5, h25]
        rw [h_sub_cast] at h_cast
        push_cast at h_cast
        exact h_cast
      have h_contra := check_mod_251 f r h_f_mod_250
      contradiction
  · -- e is odd
    by_cases hf3 : f ≥ 3
    · have h9 : 9 ∣ 3 ^ f := by
        have : f = (f - 2) + 2 := by omega
        rw [this, pow_add]
        use 3 ^ (f - 2)
        ring
      have h_zmod : (5 : ZMod 9) ^ e = 7 := by
        have : 3 ^ f = 5 ^ e + 2 := by omega
        have h_cast : ((3 ^ f : ℕ) : ZMod 9) = ((5 ^ e + 2 : ℕ) : ZMod 9) := by rw [this]
        push_cast at h_cast
        have h_div : (3 ^ f : ZMod 9) = 0 := by
          rcases h9 with ⟨c, hc⟩
          have hc_cast : ((3 ^ f : ℕ) : ZMod 9) = ((9 * c : ℕ) : ZMod 9) := congrArg Nat.cast hc
          have h_goal : (3 ^ f : ZMod 9) = ((3 ^ f : ℕ) : ZMod 9) := by push_cast; rfl
          rw [h_goal, hc_cast]
          push_cast
          have h9_zero : (9 : ZMod 9) = 0 := rfl
          rw [h9_zero, zero_mul]
        rw [h_div] at h_cast
        have h_cast2 : (5 : ZMod 9) ^ e = -2 := by
          calc (5 : ZMod 9) ^ e = ((5 : ZMod 9) ^ e + 2) - 2 := by ring
          _ = 0 - 2 := by rw [← h_cast]
          _ = -2 := by ring
        calc (5 : ZMod 9) ^ e = -2 := h_cast2
        _ = 7 := by decide
      have h_mod := (pow_five_zmod_nine e).mp h_zmod
      have : e % 2 = 0 := by
        have h_div_mod : e = 6 * (e / 6) + e % 6 := (Nat.div_add_mod e 6).symm
        rw [h_mod] at h_div_mod
        rw [h_div_mod]
        clear h he hf hf3 h9 h_zmod h_mod
        omega
      omega
    · have h_lt3 : f < 3 := Nat.not_le.mp hf3
      have h_f2 : f = 2 := by omega
      have h_ne : 5 ^ e = 7 := by
        have h_sub : 3 ^ f - 5 ^ e = 2 := h
        rw [h_f2] at h_sub
        have h32 : 3 ^ 2 = 9 := rfl
        rw [h32] at h_sub
        omega
      exact False.elim (pow_five_ne_seven e h_ne)

-- Pillai 3 5 helper proofs

open Nat

lemma pow_five_zmod_252 (f : ℕ) : (5 : ZMod 252) ^ f = (5 : ZMod 252) ^ (f % 6) := by
  have h_eq : f = 6 * (f / 6) + f % 6 := (Nat.div_add_mod f 6).symm
  have h_pow : (5 : ZMod 252) ^ f = (5 : ZMod 252) ^ (f % 6) := by
    conv_lhs => rw [h_eq]
    rw [pow_add, pow_mul]
    have : (5 : ZMod 252) ^ 6 = 1 := by decide
    rw [this, one_pow, one_mul]
  rw [h_pow]

lemma pow_three_helper (k : ℕ) : (3 : ZMod 252) ^ (6 * k) * 9 = 9 := by
  induction k with
  | zero =>
    simp only [mul_zero, pow_zero, one_mul]
  | succ k ih =>
    have h_step : 6 * (k + 1) = 6 * k + 6 := by ring
    rw [h_step, pow_add]
    have h_assoc : (3 : ZMod 252) ^ (6 * k) * 3 ^ 6 * 9 = (3 : ZMod 252) ^ (6 * k) * (3 ^ 6 * 9) := by ring
    rw [h_assoc]
    have h_decide : (3 : ZMod 252) ^ 6 * 9 = 9 := by decide
    rw [h_decide, ih]

lemma pow_three_zmod_252 (e : ℕ) (he : 1 < e) :
    (3 : ZMod 252) ^ e = (3 : ZMod 252) ^ ((e - 2) % 6 + 2) := by
  have h_eq : e = 6 * ((e - 2) / 6) + ((e - 2) % 6 + 2) := by omega
  conv_lhs => rw [h_eq]
  rw [pow_add]
  have h_eq2 : (3 : ZMod 252) ^ ((e - 2) % 6 + 2) = 9 * (3 : ZMod 252) ^ ((e - 2) % 6) := by
    have : (e - 2) % 6 + 2 = 2 + (e - 2) % 6 := by omega
    rw [this, pow_add]
    rfl
  rw [h_eq2]
  have h_assoc : (3 : ZMod 252) ^ (6 * ((e - 2) / 6)) * (9 * 3 ^ ((e - 2) % 6)) =
      ((3 : ZMod 252) ^ (6 * ((e - 2) / 6)) * 9) * 3 ^ ((e - 2) % 6) := by ring
  rw [h_assoc, pow_three_helper, ← h_eq2]

lemma pillai_diff_two_3_5 (e f : ℕ) (he : 1 < e) (_hf : 1 < f) : 5 ^ f - 3 ^ e ≠ 2 := by
  intro h
  have h_zmod : (5 : ZMod 252) ^ f - (3 : ZMod 252) ^ e = 2 := by
    have h_ge : 5 ^ f ≥ 3 ^ e := by omega
    have h_cast : ((5 ^ f - 3 ^ e : ℕ) : ZMod 252) = ((2 : ℕ) : ZMod 252) := congrArg Nat.cast h
    rw [Nat.cast_sub h_ge] at h_cast
    push_cast at h_cast
    exact h_cast
  rw [pow_five_zmod_252 f, pow_three_zmod_252 e he] at h_zmod
  have h_mod_f : f % 6 < 6 := Nat.mod_lt _ (by decide)
  have h_mod_e : (e - 2) % 6 < 6 := Nat.mod_lt _ (by decide)
  interval_cases hf_mod : f % 6 <;> interval_cases he_mod : (e - 2) % 6 <;> revert h_zmod <;> decide
lemma not_isCompositePrimePow_of_lt_four (m : ℕ) (h : m < 4) : ¬ IsCompositePrimePow m := by
  rintro ⟨p, e, hp, he, rfl⟩
  have hp2 : p ≥ 2 := hp.two_le
  have he2 : e ≥ 2 := he
  have : p ^ e ≥ 4 := by
    calc p ^ e ≥ p ^ 2 := Nat.pow_le_pow_right (by omega) he2
    _ ≥ 2 ^ 2 := Nat.pow_le_pow_left hp2 2
    _ = 4 := by decide
  omega

lemma not_isCompositePrimePow_of_prime (m : ℕ) (hp : Nat.Prime m) : ¬ IsCompositePrimePow m := by
  rw [isCompositePrimePow_iff]
  simp [hp]


lemma p_ne_three (p : ℕ) (hp : Nat.Prime p) (hp3 : p ≠ 3) : (p : ZMod 3) = 1 ∨ (p : ZMod 3) = 2 := by
  have h_ne : p % 3 ≠ 0 := by
    intro hc
    have : 3 ∣ p := Nat.dvd_of_mod_eq_zero hc
    rcases hp.eq_one_or_self_of_dvd 3 this with h1 | h2
    · contradiction
    · exact hp3 h2.symm
  have h_mod : p % 3 < 3 := Nat.mod_lt _ (by decide)
  interval_cases hp_mod : p % 3
  · contradiction
  · left
    have : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
    rw [this, hp_mod]
    rfl
  · right
    have : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
    rw [this, hp_mod]
    rfl

lemma e_odd_of_ne_three (p q e f : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (he : 1 < e) (hf : 1 < f) (h : q ^ f - p ^ e = 2) (hp3 : p ≠ 3) (hq3 : q ≠ 3) :
    e % 2 = 1 := by
  by_contra hc
  have he_even : e % 2 = 0 := by omega
  have he_eq : e = 2 * (e / 2) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero he_even)).symm
  have h_zmod : (q : ZMod 3) ^ f = 0 := by
    have h_eq : q ^ f = p ^ e + 2 := by omega
    have h_cast : ((q ^ f : ℕ) : ZMod 3) = ((p ^ e + 2 : ℕ) : ZMod 3) := congrArg Nat.cast h_eq
    push_cast at h_cast
    rw [he_eq] at h_cast
    have hp_pow : (p : ZMod 3) ^ (2 * (e / 2)) = ((p : ZMod 3) ^ 2) ^ (e / 2) := by rw [pow_mul]
    rw [hp_pow] at h_cast
    rcases p_ne_three p hp hp3 with hp1 | hp2
    · rw [hp1] at h_cast
      simp only [one_pow] at h_cast
      have : (1 : ZMod 3) + 2 = 0 := rfl
      rw [this] at h_cast
      exact h_cast
    · rw [hp2] at h_cast
      have : (2 : ZMod 3) ^ 2 = 1 := rfl
      rw [this, one_pow] at h_cast
      have : (1 : ZMod 3) + 2 = 0 := rfl
      rw [this] at h_cast
      exact h_cast
  rcases p_ne_three q hq hq3 with hq1 | hq2
  · rw [hq1] at h_zmod
    simp only [one_pow, one_ne_zero] at h_zmod
  · rw [hq2] at h_zmod
    have h_pow_ne_zero : (2 : ZMod 3) ^ f ≠ 0 := by
      rcases Nat.mod_two_eq_zero_or_one f with hf_even | hf_odd
      · have hf_eq : f = 2 * (f / 2) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hf_even)).symm
        rw [hf_eq]
        have : (2 : ZMod 3) ^ (2 * (f / 2)) = ((2 : ZMod 3) ^ 2) ^ (f / 2) := by rw [pow_mul]
        rw [this]
        have : (2 : ZMod 3) ^ 2 = 1 := rfl
        rw [this, one_pow]
        decide
      · have hf_eq : f = 2 * (f / 2) + 1 := by omega
        rw [hf_eq]
        have : (2 : ZMod 3) ^ (2 * (f / 2) + 1) = ((2 : ZMod 3) ^ 2) ^ (f / 2) * 2 := by rw [pow_succ, pow_mul]
        rw [this]
        have : (2 : ZMod 3) ^ 2 = 1 := rfl
        rw [this, one_pow, one_mul]
        decide
    exact h_pow_ne_zero h_zmod

lemma p_mod_three_eq_two_of_ne_three (p q e f : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (he : 1 < e) (hf : 1 < f) (h : q ^ f - p ^ e = 2) (hp3 : p ≠ 3) (hq3 : q ≠ 3) :
    p % 3 = 2 := by
  have he_odd := e_odd_of_ne_three p q e f hp hq he hf h hp3 hq3
  rcases p_ne_three p hp hp3 with hp1 | hp2
  · exfalso
    have h_zmod : (q : ZMod 3) ^ f = 0 := by
      have h_eq : q ^ f = p ^ e + 2 := by omega
      have h_cast : ((q ^ f : ℕ) : ZMod 3) = ((p ^ e + 2 : ℕ) : ZMod 3) := congrArg Nat.cast h_eq
      push_cast at h_cast
      rw [hp1] at h_cast
      simp only [one_pow] at h_cast
      have : (1 : ZMod 3) + 2 = 0 := rfl
      rw [this] at h_cast
      exact h_cast
    rcases p_ne_three q hq hq3 with hq1 | hq2
    · rw [hq1] at h_zmod
      simp only [one_pow, one_ne_zero] at h_zmod
    · rw [hq2] at h_zmod
      have h_pow_ne_zero : (2 : ZMod 3) ^ f ≠ 0 := by
        rcases Nat.mod_two_eq_zero_or_one f with hf_even | hf_odd
        · have hf_eq : f = 2 * (f / 2) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hf_even)).symm
          rw [hf_eq]
          have : (2 : ZMod 3) ^ (2 * (f / 2)) = ((2 : ZMod 3) ^ 2) ^ (f / 2) := by rw [pow_mul]
          rw [this]
          have : (2 : ZMod 3) ^ 2 = 1 := rfl
          rw [this, one_pow]
          decide
        · have hf_eq : f = 2 * (f / 2) + 1 := by omega
          rw [hf_eq]
          have : (2 : ZMod 3) ^ (2 * (f / 2) + 1) = ((2 : ZMod 3) ^ 2) ^ (f / 2) * 2 := by rw [pow_succ, pow_mul]
          rw [this]
          have : (2 : ZMod 3) ^ 2 = 1 := rfl
          rw [this, one_pow, one_mul]
          decide
      exact h_pow_ne_zero h_zmod
  · have h_mod : p % 3 < 3 := Nat.mod_lt _ (by decide)
    interval_cases hp_mod : p % 3
    · have : ((p : ℕ) : ZMod 3) = 0 := by
        have : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
        rw [this, hp_mod]
        rfl
      rw [this] at hp2
      contradiction
    · have : ((p : ℕ) : ZMod 3) = 1 := by
        have : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
        rw [this, hp_mod]
        rfl
      rw [this] at hp2
      contradiction
    · rfl

lemma q_mod_three_eq_one_of_f_odd (p q e f : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (he : 1 < e) (hf : 1 < f) (h : q ^ f - p ^ e = 2) (hp3 : p ≠ 3) (hq3 : q ≠ 3) (hf_odd : f % 2 = 1) :
    q % 3 = 1 := by
  have hp_mod := p_mod_three_eq_two_of_ne_three p q e f hp hq he hf h hp3 hq3
  have he_odd := e_odd_of_ne_three p q e f hp hq he hf h hp3 hq3
  have h_zmod : (q : ZMod 3) ^ f = 1 := by
    have h_eq : q ^ f = p ^ e + 2 := by omega
    have h_cast : ((q ^ f : ℕ) : ZMod 3) = ((p ^ e + 2 : ℕ) : ZMod 3) := congrArg Nat.cast h_eq
    push_cast at h_cast
    have hp_pow : (p : ZMod 3) ^ e = (p : ZMod 3) ^ (2 * (e / 2) + 1) := congrArg (fun x => (p : ZMod 3) ^ x) (by omega)
    rw [hp_pow] at h_cast
    have hp_pow2 : (p : ZMod 3) ^ (2 * (e / 2) + 1) = ((p : ZMod 3) ^ 2) ^ (e / 2) * p := by rw [pow_succ, pow_mul]
    rw [hp_pow2] at h_cast
    have hp_cast : (p : ZMod 3) = 2 := by
      have : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
      rw [this, hp_mod]
      rfl
    rw [hp_cast] at h_cast
    have : (2 : ZMod 3) ^ 2 = 1 := rfl
    rw [this, one_pow, one_mul] at h_cast
    have : (2 : ZMod 3) + 2 = 1 := rfl
    rw [this] at h_cast
    exact h_cast
  rcases p_ne_three q hq hq3 with hq1 | hq2
  · have h_mod : q % 3 < 3 := Nat.mod_lt _ (by decide)
    interval_cases hq_mod : q % 3
    · have : ((q : ℕ) : ZMod 3) = 0 := by
        have : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
        rw [this, hq_mod]
        rfl
      rw [this] at hq1
      contradiction
    · rfl
    · have : ((q : ℕ) : ZMod 3) = 2 := by
        have : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
        rw [this, hq_mod]
        rfl
      rw [this] at hq1
      contradiction
  · exfalso
    rw [hq2] at h_zmod
    have hf_eq : f = 2 * (f / 2) + 1 := by omega
    rw [hf_eq] at h_zmod
    have : (2 : ZMod 3) ^ (2 * (f / 2) + 1) = ((2 : ZMod 3) ^ 2) ^ (f / 2) * 2 := by rw [pow_succ, pow_mul]
    rw [this] at h_zmod
    have : (2 : ZMod 3) ^ 2 = 1 := rfl
    rw [this, one_pow, one_mul] at h_zmod
    have : (2 : ZMod 3) = 1 := h_zmod
    contradiction

lemma f_even_of_q_mod_three_eq_two (p q e f : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (he : 1 < e) (hf : 1 < f) (h : q ^ f - p ^ e = 2) (hp3 : p ≠ 3) (hq3 : q ≠ 3) (hq_mod : q % 3 = 2) :
    f % 2 = 0 := by
  by_contra hc
  have hf_odd : f % 2 = 1 := by omega
  have hq_mod_eq_one := q_mod_three_eq_one_of_f_odd p q e f hp hq he hf h hp3 hq3 hf_odd
  omega

lemma not_dvd_three_f_of_q3 (p e f : ℕ) (hp : Nat.Prime p) (he : 1 < e) (h : 3 ^ f - p ^ e = 2) : ¬ 3 ∣ e := by
  rintro ⟨s, rfl⟩
  have h9 : 9 ∣ 3 ^ f := by
    have hp2 : p ≥ 2 := hp.two_le
    have : p ^ (3 * s) ≥ 8 := by
      have h3s : 3 * s ≥ 3 := by omega
      calc p ^ (3 * s) ≥ p ^ 3 := Nat.pow_le_pow_right (by omega) h3s
      _ ≥ 2 ^ 3 := Nat.pow_le_pow_left hp2 3
      _ = 8 := by decide
    have : 3 ^ f ≥ 10 := by omega
    have h_f_ge3 : f ≥ 3 := by
      by_contra hc
      have : f < 3 := by omega
      interval_cases f <;> omega
    have : f = (f - 2) + 2 := by omega
    rw [this, pow_add]
    use 3 ^ (f - 2)
    ring
  rcases h9 with ⟨c, hc⟩
  have h_eq : 3 ^ f = p ^ (3 * s) + 2 := by omega
  have h_cast : ((3 ^ f : ℕ) : ZMod 9) = ((p ^ (3 * s) + 2 : ℕ) : ZMod 9) := congrArg Nat.cast h_eq
  push_cast at h_cast
  have h_div : (3 ^ f : ZMod 9) = 0 := by
    have hc_cast : ((3 ^ f : ℕ) : ZMod 9) = ((9 * c : ℕ) : ZMod 9) := congrArg Nat.cast hc
    have h_goal : (3 ^ f : ZMod 9) = ((3 ^ f : ℕ) : ZMod 9) := by push_cast; rfl
    rw [h_goal, hc_cast]
    push_cast
    have : (9 : ZMod 9) = 0 := rfl
    rw [this, zero_mul]
  rw [h_div] at h_cast
  have h_cast2 : (p : ZMod 9) ^ (3 * s) = -2 := by
    calc (p : ZMod 9) ^ (3 * s) = ((p : ZMod 9) ^ (3 * s) + 2) - 2 := by ring
    _ = 0 - 2 := by rw [← h_cast]
    _ = -2 := by ring
  have h_cube : ((p : ZMod 9) ^ s) ^ 3 = 7 := by
    calc ((p : ZMod 9) ^ s) ^ 3 = (p : ZMod 9) ^ (3 * s) := by ring
    _ = -2 := h_cast2
    _ = 7 := rfl
  set y := (p : ZMod 9) ^ s
  have h_val : y.val < 9 := y.val_lt
  have h_eq_y : y = (y.val : ZMod 9) := (ZMod.natCast_zmod_val y).symm
  rw [h_eq_y] at h_cube
  interval_cases h_y : y.val <;> revert h_cube <;> decide

lemma not_dvd_three_e_of_p3 (q e f : ℕ) (hq : Nat.Prime q) (hf : 1 < f) (h : q ^ f - 3 ^ e = 2) : ¬ 3 ∣ f := by
  rintro ⟨s, rfl⟩
  have h9 : 9 ∣ 3 ^ e := by
    have : e ≥ 2 := by
      have hq2 : q ≥ 2 := hq.two_le
      have : q ^ (3 * s) ≥ 8 := by
        have : 3 * s ≥ 3 := by omega
        calc q ^ (3 * s) ≥ q ^ 3 := Nat.pow_le_pow_right (by omega) this
        _ ≥ 2 ^ 3 := Nat.pow_le_pow_left hq2 3
        _ = 8 := by decide
      have : 3 ^ e ≥ 6 := by omega
      have : e ≥ 2 := by
        by_contra hc
        have : e < 2 := by omega
        interval_cases e <;> omega
      omega
    have : e = (e - 2) + 2 := by omega
    rw [this, pow_add]
    use 3 ^ (e - 2)
    ring
  rcases h9 with ⟨c, hc⟩
  have h_eq : q ^ (3 * s) = 3 ^ e + 2 := by omega
  have h_cast : ((q ^ (3 * s) : ℕ) : ZMod 9) = ((3 ^ e + 2 : ℕ) : ZMod 9) := congrArg Nat.cast h_eq
  push_cast at h_cast
  have h_div : (3 ^ e : ZMod 9) = 0 := by
    have hc_cast : ((3 ^ e : ℕ) : ZMod 9) = ((9 * c : ℕ) : ZMod 9) := congrArg Nat.cast hc
    have h_goal : (3 ^ e : ZMod 9) = ((3 ^ e : ℕ) : ZMod 9) := by push_cast; rfl
    rw [h_goal, hc_cast]
    push_cast
    have : (9 : ZMod 9) = 0 := rfl
    rw [this, zero_mul]
  rw [h_div, zero_add] at h_cast
  have h_cube : ((q : ZMod 9) ^ s) ^ 3 = 2 := by
    calc ((q : ZMod 9) ^ s) ^ 3 = (q : ZMod 9) ^ (3 * s) := by ring
    _ = 2 := h_cast
  set y := (q : ZMod 9) ^ s
  have h_val : y.val < 9 := y.val_lt
  have h_eq_y : y = (y.val : ZMod 9) := (ZMod.natCast_zmod_val y).symm
  rw [h_eq_y] at h_cube
  interval_cases h_y : y.val <;> revert h_cube <;> decide


lemma q_ne_p_of_diff_two (p q e f : ℕ) (hp : Nat.Prime p) (he : 1 < e) (h : q ^ f - p ^ e = 2) : q ≠ p := by
  intro hqp
  subst hqp
  have hq_pos : 0 < q := hp.pos
  by_cases hfe : f ≤ e
  · have : q ^ f - q ^ e = 0 := by
      have : q ^ f ≤ q ^ e := Nat.pow_le_pow_right hq_pos hfe
      omega
    omega
  · have hf_gt : f > e := by omega
    have h_div : q ^ e * (q ^ (f - e) - 1) = 2 := by
      calc q ^ e * (q ^ (f - e) - 1) = q ^ e * q ^ (f - e) - q ^ e * 1 := Nat.mul_sub_left_distrib (q ^ e) (q ^ (f - e)) 1
      _ = q ^ (e + (f - e)) - q ^ e := by
        have : q ^ e * q ^ (f - e) = q ^ (e + (f - e)) := (pow_add q e (f - e)).symm
        rw [this, mul_one]
      _ = q ^ f - q ^ e := by
        have : e + (f - e) = f := by omega
        rw [this]
      _ = 2 := h
    have hdvd : q ^ e ∣ 2 := by
      use q ^ (f - e) - 1
      exact h_div.symm
    have hp_ge2 : q ≥ 2 := hp.two_le
    have h_pow_ge4 : q ^ e ≥ 4 := by
      calc q ^ e ≥ q ^ 2 := Nat.pow_le_pow_right (by omega) he
      _ ≥ 2 ^ 2 := Nat.pow_le_pow_left hp_ge2 2
      _ = 4 := by decide
    have h_dvd_le : q ^ e ≤ 2 := Nat.le_of_dvd (by decide) hdvd
    omega

lemma pillai_diff_two_lt_27 (p q e f : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (he : 1 < e) (hf : 1 < f) (h : q ^ f - p ^ e = 2) (hlt : p ^ e < 27) :
    p = 5 ∧ e = 2 ∧ q = 3 ∧ f = 3 := by
  have hp_cases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p ≥ 6 := by
    have : p ≠ 0 := hp.ne_zero
    have : p ≠ 1 := hp.ne_one
    have : p ≠ 4 := by
      intro hc; subst hc; revert hp; decide
    omega
  rcases hp_cases with rfl | rfl | rfl | hp_ge6
  · -- p = 2
    exfalso
    have hq2 : q ≠ 2 := q_ne_p_of_diff_two 2 q e f hp he h
    have h_pow : 2 ^ e = 2 ^ (e - 1) * 2 := by
      have he_eq : e = (e - 1) + 1 := by omega
      conv_lhs => rw [he_eq]
      rw [pow_add, pow_one]
    have h_even : 2 ∣ q ^ f := by
      use 2 ^ (e - 1) + 1
      calc q ^ f = 2 ^ e + 2 := by omega
      _ = 2 ^ (e - 1) * 2 + 2 := by rw [h_pow]
      _ = 2 * (2 ^ (e - 1) + 1) := by ring
    have hq_div : 2 ∣ q := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h_even
    rcases hq.eq_one_or_self_of_dvd 2 hq_div with h1 | h2
    · contradiction
    · exact hq2 h2.symm
  · -- p = 3
    have he_eq2 : e = 2 := by
      by_contra hc
      have : e ≥ 3 := by omega
      have : 3 ^ e ≥ 27 := by
        calc 3 ^ e ≥ 3 ^ 3 := Nat.pow_le_pow_right (by decide) this
        _ = 27 := by decide
      omega
    have h_q_cases : q = 2 ∨ q = 3 ∨ q ≥ 4 := by
      have : q ≠ 0 := hq.ne_zero
      have : q ≠ 1 := hq.ne_one
      omega
    rcases h_q_cases with rfl | hq3 | hq_ge4
    · -- q = 2
      exfalso
      have h2f : 2 ^ f = 11 := by
        have : 3 ^ e = 9 := by rw [he_eq2]; rfl
        omega
      have hf_lt : f < 4 := by
        by_contra hc
        have h_ge4 : f ≥ 4 := by omega
        have : 2 ^ f ≥ 16 := by
          calc 2 ^ f ≥ 2 ^ 4 := Nat.pow_le_pow_right (by decide) h_ge4
          _ = 16 := by decide
        omega
      interval_cases f <;> revert h2f <;> decide
    · exfalso
      have : q = 3 := hq3
      exact q_ne_p_of_diff_two 3 q e f hp he h this
    · exfalso
      have h_qf : q ^ f = 11 := by
        have : 3 ^ e = 9 := by rw [he_eq2]; rfl
        omega
      have : q ^ f ≥ 16 := by
        have hq_pos : 0 < q := hq.pos
        calc q ^ f ≥ q ^ 2 := Nat.pow_le_pow_right hq_pos hf
        _ ≥ 4 ^ 2 := Nat.pow_le_pow_left hq_ge4 2
        _ = 16 := by decide
      omega
  · -- p = 5
    have he_eq2 : e = 2 := by
      by_contra hc
      have : e ≥ 3 := by omega
      have : 5 ^ e ≥ 125 := by
        calc 5 ^ e ≥ 5 ^ 3 := Nat.pow_le_pow_right (by decide) this
        _ = 125 := by decide
      omega
    have h_q_cases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q ≥ 6 := by
      have : q ≠ 0 := hq.ne_zero
      have : q ≠ 1 := hq.ne_one
      have : q ≠ 4 := by
        intro hc; subst hc; revert hq; decide
      omega
    rcases h_q_cases with rfl | rfl | hq5 | hq_ge6
    · exfalso
      have h2f : 2 ^ f = 27 := by
        have : 5 ^ e = 25 := by rw [he_eq2]; rfl
        omega
      have hf_lt : f < 5 := by
        by_contra hc
        have h_ge5 : f ≥ 5 := by omega
        have : 2 ^ f ≥ 32 := by
          calc 2 ^ f ≥ 2 ^ 5 := Nat.pow_le_pow_right (by decide) h_ge5
          _ = 32 := by decide
        omega
      interval_cases f <;> revert h2f <;> decide
    · have hf3 : f = 3 := by
        have : 3 ^ f = 27 := by
          have : 5 ^ e = 25 := by rw [he_eq2]; rfl
          omega
        exact pow_three_eq_27 f this
      exact ⟨rfl, he_eq2, rfl, hf3⟩
    · exfalso
      have : q = 5 := hq5
      exact q_ne_p_of_diff_two 5 q e f hp he h this
    · exfalso
      have h_qf : q ^ f = 27 := by
        have : 5 ^ e = 25 := by rw [he_eq2]; rfl
        omega
      have h_qf_ge : q ^ f ≥ 36 := by
        have hq_pos : 0 < q := hq.pos
        calc q ^ f ≥ q ^ 2 := Nat.pow_le_pow_right hq_pos hf
        _ ≥ 6 ^ 2 := Nat.pow_le_pow_left hq_ge6 2
        _ = 36 := by decide
      omega
  · exfalso
    have : p ^ e ≥ 36 := by
      have hp_pos : 0 < p := hp.pos
      calc p ^ e ≥ p ^ 2 := Nat.pow_le_pow_right hp_pos he
      _ ≥ 6 ^ 2 := Nat.pow_le_pow_left hp_ge6 2
      _ = 36 := by decide
    omega



-- Auxiliary Lemmas from Test.lean

lemma coprime_252_of_prime (q : ℕ) (hq : Nat.Prime q) (hq2 : q ≠ 2) (hq3 : q ≠ 3) (hq7 : q ≠ 7) :
    q % 252 ≠ 0 ∧ Nat.Coprime q 252 := by
  have h_gcd : q.gcd 252 = 1 := by
    by_contra hc
    have h_dvd : q.gcd 252 ∣ q := q.gcd_dvd_left 252
    have h_dvd2 : q.gcd 252 ∣ 252 := q.gcd_dvd_right 252
    rcases hq.eq_one_or_self_of_dvd _ h_dvd with h1 | h2
    · exact hc h1
    · have hq_dvd_252 : q ∣ 252 := h2 ▸ h_dvd2
      have hq252 : q ≤ 252 := Nat.le_of_dvd (by decide) hq_dvd_252
      interval_cases q
      · exact (show ¬ Nat.Prime 0 by decide) hq
      · exact (show ¬ Nat.Prime 1 by decide) hq
      · exact hq2 rfl
      · exact hq3 rfl
      · exact (show ¬ Nat.Prime 4 by decide) hq
      · exact (show ¬ 5 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 6 by decide) hq
      · exact hq7 rfl
      · exact (show ¬ Nat.Prime 8 by decide) hq
      · exact (show ¬ Nat.Prime 9 by decide) hq
      · exact (show ¬ Nat.Prime 10 by decide) hq
      · exact (show ¬ 11 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 12 by decide) hq
      · exact (show ¬ 13 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 14 by decide) hq
      · exact (show ¬ Nat.Prime 15 by decide) hq
      · exact (show ¬ Nat.Prime 16 by decide) hq
      · exact (show ¬ 17 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 18 by decide) hq
      · exact (show ¬ 19 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 20 by decide) hq
      · exact (show ¬ Nat.Prime 21 by decide) hq
      · exact (show ¬ Nat.Prime 22 by decide) hq
      · exact (show ¬ 23 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 24 by decide) hq
      · exact (show ¬ Nat.Prime 25 by decide) hq
      · exact (show ¬ Nat.Prime 26 by decide) hq
      · exact (show ¬ Nat.Prime 27 by decide) hq
      · exact (show ¬ Nat.Prime 28 by decide) hq
      · exact (show ¬ 29 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 30 by decide) hq
      · exact (show ¬ 31 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 32 by decide) hq
      · exact (show ¬ Nat.Prime 33 by decide) hq
      · exact (show ¬ Nat.Prime 34 by decide) hq
      · exact (show ¬ Nat.Prime 35 by decide) hq
      · exact (show ¬ Nat.Prime 36 by decide) hq
      · exact (show ¬ 37 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 38 by decide) hq
      · exact (show ¬ Nat.Prime 39 by decide) hq
      · exact (show ¬ Nat.Prime 40 by decide) hq
      · exact (show ¬ 41 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 42 by decide) hq
      · exact (show ¬ 43 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 44 by decide) hq
      · exact (show ¬ Nat.Prime 45 by decide) hq
      · exact (show ¬ Nat.Prime 46 by decide) hq
      · exact (show ¬ 47 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 48 by decide) hq
      · exact (show ¬ Nat.Prime 49 by decide) hq
      · exact (show ¬ Nat.Prime 50 by decide) hq
      · exact (show ¬ Nat.Prime 51 by decide) hq
      · exact (show ¬ Nat.Prime 52 by decide) hq
      · exact (show ¬ 53 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 54 by decide) hq
      · exact (show ¬ Nat.Prime 55 by decide) hq
      · exact (show ¬ Nat.Prime 56 by decide) hq
      · exact (show ¬ Nat.Prime 57 by decide) hq
      · exact (show ¬ Nat.Prime 58 by decide) hq
      · exact (show ¬ 59 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 60 by decide) hq
      · exact (show ¬ 61 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 62 by decide) hq
      · exact (show ¬ Nat.Prime 63 by decide) hq
      · exact (show ¬ Nat.Prime 64 by decide) hq
      · exact (show ¬ Nat.Prime 65 by decide) hq
      · exact (show ¬ Nat.Prime 66 by decide) hq
      · exact (show ¬ 67 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 68 by decide) hq
      · exact (show ¬ Nat.Prime 69 by decide) hq
      · exact (show ¬ Nat.Prime 70 by decide) hq
      · exact (show ¬ 71 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 72 by decide) hq
      · exact (show ¬ 73 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 74 by decide) hq
      · exact (show ¬ Nat.Prime 75 by decide) hq
      · exact (show ¬ Nat.Prime 76 by decide) hq
      · exact (show ¬ Nat.Prime 77 by decide) hq
      · exact (show ¬ Nat.Prime 78 by decide) hq
      · exact (show ¬ 79 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 80 by decide) hq
      · exact (show ¬ Nat.Prime 81 by decide) hq
      · exact (show ¬ Nat.Prime 82 by decide) hq
      · exact (show ¬ 83 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 84 by decide) hq
      · exact (show ¬ Nat.Prime 85 by decide) hq
      · exact (show ¬ Nat.Prime 86 by decide) hq
      · exact (show ¬ Nat.Prime 87 by decide) hq
      · exact (show ¬ Nat.Prime 88 by decide) hq
      · exact (show ¬ 89 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 90 by decide) hq
      · exact (show ¬ Nat.Prime 91 by decide) hq
      · exact (show ¬ Nat.Prime 92 by decide) hq
      · exact (show ¬ Nat.Prime 93 by decide) hq
      · exact (show ¬ Nat.Prime 94 by decide) hq
      · exact (show ¬ Nat.Prime 95 by decide) hq
      · exact (show ¬ Nat.Prime 96 by decide) hq
      · exact (show ¬ 97 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 98 by decide) hq
      · exact (show ¬ Nat.Prime 99 by decide) hq
      · exact (show ¬ Nat.Prime 100 by decide) hq
      · exact (show ¬ 101 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 102 by decide) hq
      · exact (show ¬ 103 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 104 by decide) hq
      · exact (show ¬ Nat.Prime 105 by decide) hq
      · exact (show ¬ Nat.Prime 106 by decide) hq
      · exact (show ¬ 107 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 108 by decide) hq
      · exact (show ¬ 109 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 110 by decide) hq
      · exact (show ¬ Nat.Prime 111 by decide) hq
      · exact (show ¬ Nat.Prime 112 by decide) hq
      · exact (show ¬ 113 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 114 by decide) hq
      · exact (show ¬ Nat.Prime 115 by decide) hq
      · exact (show ¬ Nat.Prime 116 by decide) hq
      · exact (show ¬ Nat.Prime 117 by decide) hq
      · exact (show ¬ Nat.Prime 118 by decide) hq
      · exact (show ¬ Nat.Prime 119 by decide) hq
      · exact (show ¬ Nat.Prime 120 by decide) hq
      · exact (show ¬ Nat.Prime 121 by decide) hq
      · exact (show ¬ Nat.Prime 122 by decide) hq
      · exact (show ¬ Nat.Prime 123 by decide) hq
      · exact (show ¬ Nat.Prime 124 by decide) hq
      · exact (show ¬ Nat.Prime 125 by decide) hq
      · exact (show ¬ Nat.Prime 126 by decide) hq
      · exact (show ¬ 127 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 128 by decide) hq
      · exact (show ¬ Nat.Prime 129 by decide) hq
      · exact (show ¬ Nat.Prime 130 by decide) hq
      · exact (show ¬ 131 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 132 by decide) hq
      · exact (show ¬ Nat.Prime 133 by decide) hq
      · exact (show ¬ Nat.Prime 134 by decide) hq
      · exact (show ¬ Nat.Prime 135 by decide) hq
      · exact (show ¬ Nat.Prime 136 by decide) hq
      · exact (show ¬ 137 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 138 by decide) hq
      · exact (show ¬ 139 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 140 by decide) hq
      · exact (show ¬ Nat.Prime 141 by decide) hq
      · exact (show ¬ Nat.Prime 142 by decide) hq
      · exact (show ¬ Nat.Prime 143 by decide) hq
      · exact (show ¬ Nat.Prime 144 by decide) hq
      · exact (show ¬ Nat.Prime 145 by decide) hq
      · exact (show ¬ Nat.Prime 146 by decide) hq
      · exact (show ¬ Nat.Prime 147 by decide) hq
      · exact (show ¬ Nat.Prime 148 by decide) hq
      · exact (show ¬ 149 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 150 by decide) hq
      · exact (show ¬ 151 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 152 by decide) hq
      · exact (show ¬ Nat.Prime 153 by decide) hq
      · exact (show ¬ Nat.Prime 154 by decide) hq
      · exact (show ¬ Nat.Prime 155 by decide) hq
      · exact (show ¬ Nat.Prime 156 by decide) hq
      · exact (show ¬ 157 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 158 by decide) hq
      · exact (show ¬ Nat.Prime 159 by decide) hq
      · exact (show ¬ Nat.Prime 160 by decide) hq
      · exact (show ¬ Nat.Prime 161 by decide) hq
      · exact (show ¬ Nat.Prime 162 by decide) hq
      · exact (show ¬ 163 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 164 by decide) hq
      · exact (show ¬ Nat.Prime 165 by decide) hq
      · exact (show ¬ Nat.Prime 166 by decide) hq
      · exact (show ¬ 167 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 168 by decide) hq
      · exact (show ¬ Nat.Prime 169 by decide) hq
      · exact (show ¬ Nat.Prime 170 by decide) hq
      · exact (show ¬ Nat.Prime 171 by decide) hq
      · exact (show ¬ Nat.Prime 172 by decide) hq
      · exact (show ¬ 173 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 174 by decide) hq
      · exact (show ¬ Nat.Prime 175 by decide) hq
      · exact (show ¬ Nat.Prime 176 by decide) hq
      · exact (show ¬ Nat.Prime 177 by decide) hq
      · exact (show ¬ Nat.Prime 178 by decide) hq
      · exact (show ¬ 179 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 180 by decide) hq
      · exact (show ¬ 181 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 182 by decide) hq
      · exact (show ¬ Nat.Prime 183 by decide) hq
      · exact (show ¬ Nat.Prime 184 by decide) hq
      · exact (show ¬ Nat.Prime 185 by decide) hq
      · exact (show ¬ Nat.Prime 186 by decide) hq
      · exact (show ¬ Nat.Prime 187 by decide) hq
      · exact (show ¬ Nat.Prime 188 by decide) hq
      · exact (show ¬ Nat.Prime 189 by decide) hq
      · exact (show ¬ Nat.Prime 190 by decide) hq
      · exact (show ¬ 191 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 192 by decide) hq
      · exact (show ¬ 193 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 194 by decide) hq
      · exact (show ¬ Nat.Prime 195 by decide) hq
      · exact (show ¬ Nat.Prime 196 by decide) hq
      · exact (show ¬ 197 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 198 by decide) hq
      · exact (show ¬ 199 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 200 by decide) hq
      · exact (show ¬ Nat.Prime 201 by decide) hq
      · exact (show ¬ Nat.Prime 202 by decide) hq
      · exact (show ¬ Nat.Prime 203 by decide) hq
      · exact (show ¬ Nat.Prime 204 by decide) hq
      · exact (show ¬ Nat.Prime 205 by decide) hq
      · exact (show ¬ Nat.Prime 206 by decide) hq
      · exact (show ¬ Nat.Prime 207 by decide) hq
      · exact (show ¬ Nat.Prime 208 by decide) hq
      · exact (show ¬ Nat.Prime 209 by decide) hq
      · exact (show ¬ Nat.Prime 210 by decide) hq
      · exact (show ¬ 211 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 212 by decide) hq
      · exact (show ¬ Nat.Prime 213 by decide) hq
      · exact (show ¬ Nat.Prime 214 by decide) hq
      · exact (show ¬ Nat.Prime 215 by decide) hq
      · exact (show ¬ Nat.Prime 216 by decide) hq
      · exact (show ¬ Nat.Prime 217 by decide) hq
      · exact (show ¬ Nat.Prime 218 by decide) hq
      · exact (show ¬ Nat.Prime 219 by decide) hq
      · exact (show ¬ Nat.Prime 220 by decide) hq
      · exact (show ¬ Nat.Prime 221 by decide) hq
      · exact (show ¬ Nat.Prime 222 by decide) hq
      · exact (show ¬ 223 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 224 by decide) hq
      · exact (show ¬ Nat.Prime 225 by decide) hq
      · exact (show ¬ Nat.Prime 226 by decide) hq
      · exact (show ¬ 227 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 228 by decide) hq
      · exact (show ¬ 229 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 230 by decide) hq
      · exact (show ¬ Nat.Prime 231 by decide) hq
      · exact (show ¬ Nat.Prime 232 by decide) hq
      · exact (show ¬ 233 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 234 by decide) hq
      · exact (show ¬ Nat.Prime 235 by decide) hq
      · exact (show ¬ Nat.Prime 236 by decide) hq
      · exact (show ¬ Nat.Prime 237 by decide) hq
      · exact (show ¬ Nat.Prime 238 by decide) hq
      · exact (show ¬ 239 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 240 by decide) hq
      · exact (show ¬ 241 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 242 by decide) hq
      · exact (show ¬ Nat.Prime 243 by decide) hq
      · exact (show ¬ Nat.Prime 244 by decide) hq
      · exact (show ¬ Nat.Prime 245 by decide) hq
      · exact (show ¬ Nat.Prime 246 by decide) hq
      · exact (show ¬ Nat.Prime 247 by decide) hq
      · exact (show ¬ Nat.Prime 248 by decide) hq
      · exact (show ¬ Nat.Prime 249 by decide) hq
      · exact (show ¬ Nat.Prime 250 by decide) hq
      · exact (show ¬ 251 ∣ 252 by decide) hq_dvd_252
      · exact (show ¬ Nat.Prime 252 by decide) hq
  have h_mod : q % 252 ≠ 0 := by
    intro hc
    have : 252 ∣ q := Nat.dvd_of_mod_eq_zero hc
    have : q.gcd 252 = 252 := Nat.gcd_eq_right this
    omega
  exact ⟨h_mod, h_gcd⟩
lemma pow_six_zmod_252 (q : ℕ) (hq_coprime : Nat.Coprime q 252) : (q : ZMod 252) ^ 6 = 1 := by
  set r := q % 252
  have hr_lt : r < 252 := Nat.mod_lt q (by decide)
  have q_mod : q % 252 = r := rfl
  interval_cases r
  · exfalso
    have h_gcd_dvd : 252 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 252 ∣ 252 := by decide
      have h_g_dvd_r : 252 ∣ 0 := by decide
      have h_g_dvd_q : 252 ∣ q := by
        have : q = 252 * (q / 252) + 0 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 252 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 1 := by
      have : q % 252 = 1 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 2 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 2 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 3 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 3 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 4 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 4 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 5 := by
      have : q % 252 = 5 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 6 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 6 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 7 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 7 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 8 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 8 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 9 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 9 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 10 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 10 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 11 := by
      have : q % 252 = 11 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 12 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 12 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 13 := by
      have : q % 252 = 13 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 14 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 14 ∣ 252 := by decide
      have h_g_dvd_r : 14 ∣ 14 := by decide
      have h_g_dvd_q : 14 ∣ q := by
        have : q = 252 * (q / 252) + 14 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 14 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 15 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 15 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 16 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 16 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 17 := by
      have : q % 252 = 17 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 18 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 18 ∣ 252 := by decide
      have h_g_dvd_r : 18 ∣ 18 := by decide
      have h_g_dvd_q : 18 ∣ q := by
        have : q = 252 * (q / 252) + 18 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 18 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 19 := by
      have : q % 252 = 19 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 20 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 20 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 21 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 21 ∣ 252 := by decide
      have h_g_dvd_r : 21 ∣ 21 := by decide
      have h_g_dvd_q : 21 ∣ q := by
        have : q = 252 * (q / 252) + 21 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 21 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 22 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 22 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 23 := by
      have : q % 252 = 23 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 24 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 24 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 25 := by
      have : q % 252 = 25 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 26 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 26 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 27 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 27 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 28 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 28 ∣ 252 := by decide
      have h_g_dvd_r : 28 ∣ 28 := by decide
      have h_g_dvd_q : 28 ∣ q := by
        have : q = 252 * (q / 252) + 28 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 28 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 29 := by
      have : q % 252 = 29 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 30 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 30 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 31 := by
      have : q % 252 = 31 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 32 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 32 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 33 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 33 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 34 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 34 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 35 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 35 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 36 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 36 ∣ 252 := by decide
      have h_g_dvd_r : 36 ∣ 36 := by decide
      have h_g_dvd_q : 36 ∣ q := by
        have : q = 252 * (q / 252) + 36 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 36 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 37 := by
      have : q % 252 = 37 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 38 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 38 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 39 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 39 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 40 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 40 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 41 := by
      have : q % 252 = 41 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 42 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 42 ∣ 252 := by decide
      have h_g_dvd_r : 42 ∣ 42 := by decide
      have h_g_dvd_q : 42 ∣ q := by
        have : q = 252 * (q / 252) + 42 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 42 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 43 := by
      have : q % 252 = 43 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 44 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 44 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 45 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 45 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 46 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 46 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 47 := by
      have : q % 252 = 47 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 48 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 48 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 49 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 49 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 50 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 50 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 51 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 51 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 52 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 52 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 53 := by
      have : q % 252 = 53 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 18 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 18 ∣ 252 := by decide
      have h_g_dvd_r : 18 ∣ 54 := by decide
      have h_g_dvd_q : 18 ∣ q := by
        have : q = 252 * (q / 252) + 54 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 18 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 55 := by
      have : q % 252 = 55 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 28 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 28 ∣ 252 := by decide
      have h_g_dvd_r : 28 ∣ 56 := by decide
      have h_g_dvd_q : 28 ∣ q := by
        have : q = 252 * (q / 252) + 56 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 28 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 57 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 57 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 58 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 58 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 59 := by
      have : q % 252 = 59 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 60 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 60 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 61 := by
      have : q % 252 = 61 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 62 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 62 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 63 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 63 ∣ 252 := by decide
      have h_g_dvd_r : 63 ∣ 63 := by decide
      have h_g_dvd_q : 63 ∣ q := by
        have : q = 252 * (q / 252) + 63 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 63 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 64 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 64 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 65 := by
      have : q % 252 = 65 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 66 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 66 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 67 := by
      have : q % 252 = 67 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 68 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 68 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 69 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 69 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 14 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 14 ∣ 252 := by decide
      have h_g_dvd_r : 14 ∣ 70 := by decide
      have h_g_dvd_q : 14 ∣ q := by
        have : q = 252 * (q / 252) + 70 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 14 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 71 := by
      have : q % 252 = 71 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 36 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 36 ∣ 252 := by decide
      have h_g_dvd_r : 36 ∣ 72 := by decide
      have h_g_dvd_q : 36 ∣ q := by
        have : q = 252 * (q / 252) + 72 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 36 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 73 := by
      have : q % 252 = 73 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 74 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 74 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 75 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 75 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 76 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 76 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 77 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 77 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 78 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 78 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 79 := by
      have : q % 252 = 79 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 80 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 80 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 81 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 81 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 82 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 82 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 83 := by
      have : q % 252 = 83 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 84 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 84 ∣ 252 := by decide
      have h_g_dvd_r : 84 ∣ 84 := by decide
      have h_g_dvd_q : 84 ∣ q := by
        have : q = 252 * (q / 252) + 84 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 84 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 85 := by
      have : q % 252 = 85 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 86 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 86 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 87 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 87 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 88 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 88 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 89 := by
      have : q % 252 = 89 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 18 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 18 ∣ 252 := by decide
      have h_g_dvd_r : 18 ∣ 90 := by decide
      have h_g_dvd_q : 18 ∣ q := by
        have : q = 252 * (q / 252) + 90 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 18 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 91 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 91 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 92 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 92 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 93 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 93 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 94 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 94 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 95 := by
      have : q % 252 = 95 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 96 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 96 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 97 := by
      have : q % 252 = 97 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 14 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 14 ∣ 252 := by decide
      have h_g_dvd_r : 14 ∣ 98 := by decide
      have h_g_dvd_q : 14 ∣ q := by
        have : q = 252 * (q / 252) + 98 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 14 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 99 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 99 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 100 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 100 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 101 := by
      have : q % 252 = 101 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 102 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 102 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 103 := by
      have : q % 252 = 103 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 104 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 104 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 21 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 21 ∣ 252 := by decide
      have h_g_dvd_r : 21 ∣ 105 := by decide
      have h_g_dvd_q : 21 ∣ q := by
        have : q = 252 * (q / 252) + 105 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 21 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 106 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 106 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 107 := by
      have : q % 252 = 107 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 36 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 36 ∣ 252 := by decide
      have h_g_dvd_r : 36 ∣ 108 := by decide
      have h_g_dvd_q : 36 ∣ q := by
        have : q = 252 * (q / 252) + 108 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 36 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 109 := by
      have : q % 252 = 109 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 110 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 110 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 111 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 111 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 28 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 28 ∣ 252 := by decide
      have h_g_dvd_r : 28 ∣ 112 := by decide
      have h_g_dvd_q : 28 ∣ q := by
        have : q = 252 * (q / 252) + 112 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 28 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 113 := by
      have : q % 252 = 113 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 114 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 114 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 115 := by
      have : q % 252 = 115 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 116 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 116 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 117 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 117 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 118 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 118 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 119 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 119 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 120 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 120 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 121 := by
      have : q % 252 = 121 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 122 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 122 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 123 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 123 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 124 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 124 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 125 := by
      have : q % 252 = 125 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 126 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 126 ∣ 252 := by decide
      have h_g_dvd_r : 126 ∣ 126 := by decide
      have h_g_dvd_q : 126 ∣ q := by
        have : q = 252 * (q / 252) + 126 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 126 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 127 := by
      have : q % 252 = 127 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 128 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 128 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 129 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 129 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 130 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 130 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 131 := by
      have : q % 252 = 131 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 132 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 132 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 133 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 133 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 134 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 134 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 135 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 135 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 136 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 136 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 137 := by
      have : q % 252 = 137 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 138 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 138 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 139 := by
      have : q % 252 = 139 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 28 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 28 ∣ 252 := by decide
      have h_g_dvd_r : 28 ∣ 140 := by decide
      have h_g_dvd_q : 28 ∣ q := by
        have : q = 252 * (q / 252) + 140 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 28 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 141 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 141 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 142 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 142 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 143 := by
      have : q % 252 = 143 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 36 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 36 ∣ 252 := by decide
      have h_g_dvd_r : 36 ∣ 144 := by decide
      have h_g_dvd_q : 36 ∣ q := by
        have : q = 252 * (q / 252) + 144 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 36 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 145 := by
      have : q % 252 = 145 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 146 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 146 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 21 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 21 ∣ 252 := by decide
      have h_g_dvd_r : 21 ∣ 147 := by decide
      have h_g_dvd_q : 21 ∣ q := by
        have : q = 252 * (q / 252) + 147 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 21 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 148 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 148 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 149 := by
      have : q % 252 = 149 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 150 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 150 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 151 := by
      have : q % 252 = 151 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 152 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 152 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 153 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 153 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 14 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 14 ∣ 252 := by decide
      have h_g_dvd_r : 14 ∣ 154 := by decide
      have h_g_dvd_q : 14 ∣ q := by
        have : q = 252 * (q / 252) + 154 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 14 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 155 := by
      have : q % 252 = 155 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 156 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 156 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 157 := by
      have : q % 252 = 157 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 158 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 158 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 159 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 159 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 160 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 160 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 161 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 161 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 18 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 18 ∣ 252 := by decide
      have h_g_dvd_r : 18 ∣ 162 := by decide
      have h_g_dvd_q : 18 ∣ q := by
        have : q = 252 * (q / 252) + 162 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 18 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 163 := by
      have : q % 252 = 163 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 164 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 164 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 165 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 165 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 166 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 166 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 167 := by
      have : q % 252 = 167 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 84 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 84 ∣ 252 := by decide
      have h_g_dvd_r : 84 ∣ 168 := by decide
      have h_g_dvd_q : 84 ∣ q := by
        have : q = 252 * (q / 252) + 168 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 84 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 169 := by
      have : q % 252 = 169 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 170 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 170 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 171 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 171 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 172 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 172 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 173 := by
      have : q % 252 = 173 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 174 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 174 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 175 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 175 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 176 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 176 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 177 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 177 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 178 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 178 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 179 := by
      have : q % 252 = 179 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 36 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 36 ∣ 252 := by decide
      have h_g_dvd_r : 36 ∣ 180 := by decide
      have h_g_dvd_q : 36 ∣ q := by
        have : q = 252 * (q / 252) + 180 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 36 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 181 := by
      have : q % 252 = 181 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 14 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 14 ∣ 252 := by decide
      have h_g_dvd_r : 14 ∣ 182 := by decide
      have h_g_dvd_q : 14 ∣ q := by
        have : q = 252 * (q / 252) + 182 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 14 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 183 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 183 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 184 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 184 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 185 := by
      have : q % 252 = 185 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 186 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 186 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 187 := by
      have : q % 252 = 187 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 188 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 188 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 63 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 63 ∣ 252 := by decide
      have h_g_dvd_r : 63 ∣ 189 := by decide
      have h_g_dvd_q : 63 ∣ q := by
        have : q = 252 * (q / 252) + 189 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 63 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 190 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 190 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 191 := by
      have : q % 252 = 191 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 192 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 192 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 193 := by
      have : q % 252 = 193 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 194 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 194 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 195 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 195 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 28 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 28 ∣ 252 := by decide
      have h_g_dvd_r : 28 ∣ 196 := by decide
      have h_g_dvd_q : 28 ∣ q := by
        have : q = 252 * (q / 252) + 196 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 28 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 197 := by
      have : q % 252 = 197 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 18 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 18 ∣ 252 := by decide
      have h_g_dvd_r : 18 ∣ 198 := by decide
      have h_g_dvd_q : 18 ∣ q := by
        have : q = 252 * (q / 252) + 198 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 18 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 199 := by
      have : q % 252 = 199 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 200 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 200 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 201 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 201 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 202 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 202 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 203 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 203 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 204 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 204 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 205 := by
      have : q % 252 = 205 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 206 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 206 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 207 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 207 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 208 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 208 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 209 := by
      have : q % 252 = 209 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 42 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 42 ∣ 252 := by decide
      have h_g_dvd_r : 42 ∣ 210 := by decide
      have h_g_dvd_q : 42 ∣ q := by
        have : q = 252 * (q / 252) + 210 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 42 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 211 := by
      have : q % 252 = 211 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 212 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 212 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 213 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 213 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 214 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 214 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 215 := by
      have : q % 252 = 215 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 36 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 36 ∣ 252 := by decide
      have h_g_dvd_r : 36 ∣ 216 := by decide
      have h_g_dvd_q : 36 ∣ q := by
        have : q = 252 * (q / 252) + 216 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 36 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 217 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 217 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 218 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 218 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 219 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 219 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 220 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 220 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 221 := by
      have : q % 252 = 221 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 222 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 222 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 223 := by
      have : q % 252 = 223 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 28 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 28 ∣ 252 := by decide
      have h_g_dvd_r : 28 ∣ 224 := by decide
      have h_g_dvd_q : 28 ∣ q := by
        have : q = 252 * (q / 252) + 224 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 28 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 225 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 225 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 226 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 226 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 227 := by
      have : q % 252 = 227 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 228 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 228 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 229 := by
      have : q % 252 = 229 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 230 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 230 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 21 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 21 ∣ 252 := by decide
      have h_g_dvd_r : 21 ∣ 231 := by decide
      have h_g_dvd_q : 21 ∣ q := by
        have : q = 252 * (q / 252) + 231 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 21 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 232 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 232 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 233 := by
      have : q % 252 = 233 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 18 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 18 ∣ 252 := by decide
      have h_g_dvd_r : 18 ∣ 234 := by decide
      have h_g_dvd_q : 18 ∣ q := by
        have : q = 252 * (q / 252) + 234 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 18 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 235 := by
      have : q % 252 = 235 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 236 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 236 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 237 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 237 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 14 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 14 ∣ 252 := by decide
      have h_g_dvd_r : 14 ∣ 238 := by decide
      have h_g_dvd_q : 14 ∣ q := by
        have : q = 252 * (q / 252) + 238 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 14 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 239 := by
      have : q % 252 = 239 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 12 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 12 ∣ 252 := by decide
      have h_g_dvd_r : 12 ∣ 240 := by decide
      have h_g_dvd_q : 12 ∣ q := by
        have : q = 252 * (q / 252) + 240 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 12 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 241 := by
      have : q % 252 = 241 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 242 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 242 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 9 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 9 ∣ 252 := by decide
      have h_g_dvd_r : 9 ∣ 243 := by decide
      have h_g_dvd_q : 9 ∣ q := by
        have : q = 252 * (q / 252) + 243 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 9 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 244 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 244 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 7 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 7 ∣ 252 := by decide
      have h_g_dvd_r : 7 ∣ 245 := by decide
      have h_g_dvd_q : 7 ∣ q := by
        have : q = 252 * (q / 252) + 245 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 7 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 6 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 6 ∣ 252 := by decide
      have h_g_dvd_r : 6 ∣ 246 := by decide
      have h_g_dvd_q : 6 ∣ q := by
        have : q = 252 * (q / 252) + 246 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 6 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 247 := by
      have : q % 252 = 247 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
  · exfalso
    have h_gcd_dvd : 4 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 4 ∣ 252 := by decide
      have h_g_dvd_r : 4 ∣ 248 := by decide
      have h_g_dvd_q : 4 ∣ q := by
        have : q = 252 * (q / 252) + 248 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 4 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 3 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 3 ∣ 252 := by decide
      have h_g_dvd_r : 3 ∣ 249 := by decide
      have h_g_dvd_q : 3 ∣ q := by
        have : q = 252 * (q / 252) + 249 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 3 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · exfalso
    have h_gcd_dvd : 2 ∣ q.gcd 252 := by
      have h_g_dvd_252 : 2 ∣ 252 := by decide
      have h_g_dvd_r : 2 ∣ 250 := by decide
      have h_g_dvd_q : 2 ∣ q := by
        have : q = 252 * (q / 252) + 250 := (Nat.div_add_mod q 252).symm.trans (by omega)
        rw [this]
        exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_252 _) h_g_dvd_r
      exact Nat.dvd_gcd h_g_dvd_q h_g_dvd_252
    have h_gcd_1 : q.gcd 252 = 1 := hq_coprime
    rw [h_gcd_1] at h_gcd_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h_gcd_dvd
    revert this
    decide
  · have : (q : ZMod 252) = 251 := by
      have : q % 252 = 251 := q_mod
      have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]
      rw [h_cast, this]
      rfl
    rw [this]
    decide
lemma pow_unit_zmod_252 (q : ℕ) (hq_coprime : Nat.Coprime q 252) (f : ℕ) :
    (q : ZMod 252) ^ f = (q : ZMod 252) ^ (f % 6) := by
  have h_eq : f = 6 * (f / 6) + f % 6 := (Nat.div_add_mod f 6).symm
  conv_lhs => rw [h_eq]
  rw [pow_add, pow_mul, pow_six_zmod_252 q hq_coprime, one_pow, one_mul]
lemma pillai_diff_two_3_7 (e f : ℕ) (he : 1 < e) (h : 7 ^ f - 3 ^ e = 2) : False := by
  have he2 : e ≥ 2 := he
  have h_zmod : (7 : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := by
    have h_ge : 7 ^ f ≥ 3 ^ e := by omega
    have h_cast : ((7 ^ f - 3 ^ e : ℕ) : ZMod 9) = ((2 : ℕ) : ZMod 9) := congrArg Nat.cast h
    rw [Nat.cast_sub h_ge] at h_cast
    push_cast at h_cast
    exact h_cast
  have h3e : (3 : ZMod 9) ^ e = 0 := by
    have he_eq : e = (e - 2) + 2 := by omega
    rw [he_eq, pow_add]
    have : (3 : ZMod 9) ^ 2 = 0 := by rfl
    rw [this, mul_zero]
  rw [h3e, sub_zero] at h_zmod
  have h7f : (7 : ZMod 9) ^ f = (7 : ZMod 9) ^ (f % 3) := by
    have h_eq : f = 3 * (f / 3) + f % 3 := (Nat.div_add_mod f 3).symm
    conv_lhs => rw [h_eq]
    rw [pow_add, pow_mul]
    have : (7 : ZMod 9) ^ 3 = 1 := by rfl
    rw [this, one_pow, one_mul]
  rw [h7f] at h_zmod
  have h_mod : f % 3 < 3 := Nat.mod_lt _ (by decide)
  interval_cases hf_mod : f % 3 <;> revert h_zmod <;> decide

lemma pillai_diff_two_5_7 (e f : ℕ) (he : 1 < e) (h : 7 ^ f - 5 ^ e = 2) : False := by
  have he2 : e ≥ 2 := he
  have h_zmod : (7 : ZMod 25) ^ f - (5 : ZMod 25) ^ e = 2 := by
    have h_ge : 7 ^ f ≥ 5 ^ e := by omega
    have h_cast : ((7 ^ f - 5 ^ e : ℕ) : ZMod 25) = ((2 : ℕ) : ZMod 25) := congrArg Nat.cast h
    rw [Nat.cast_sub h_ge] at h_cast
    push_cast at h_cast
    exact h_cast
  have h5e : (5 : ZMod 25) ^ e = 0 := by
    have he_eq : e = (e - 2) + 2 := by omega
    rw [he_eq, pow_add]
    have : (5 : ZMod 25) ^ 2 = 0 := by rfl
    rw [this, mul_zero]
  rw [h5e, sub_zero] at h_zmod
  have h7f : (7 : ZMod 25) ^ f = (7 : ZMod 25) ^ (f % 4) := by
    have h_eq : f = 4 * (f / 4) + f % 4 := (Nat.div_add_mod f 4).symm
    conv_lhs => rw [h_eq]
    rw [pow_add, pow_mul]
    have : (7 : ZMod 25) ^ 4 = 1 := by rfl
    rw [this, one_pow, one_mul]
  rw [h7f] at h_zmod
  have h_mod : f % 4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases hf_mod : f % 4 <;> revert h_zmod <;> decide

lemma pillai_diff_two_7_5 (e f : ℕ) (h : 5 ^ f - 7 ^ e = 2) : False := by
  have h_zmod : (5 : ZMod 3) ^ f - (7 : ZMod 3) ^ e = 2 := by
    have h_ge : 5 ^ f ≥ 7 ^ e := by omega
    have h_cast : ((5 ^ f - 7 ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h
    rw [Nat.cast_sub h_ge] at h_cast
    push_cast at h_cast
    exact h_cast
  have h5 : (5 : ZMod 3) = 2 := rfl
  have h7 : (7 : ZMod 3) = 1 := rfl
  rw [h5, h7, one_pow] at h_zmod
  have h2f : (2 : ZMod 3) ^ f = (2 : ZMod 3) ^ (f % 2) := by
    have h_eq : f = 2 * (f / 2) + f % 2 := (Nat.div_add_mod f 2).symm
    conv_lhs => rw [h_eq]
    rw [pow_add, pow_mul]
    have : (2 : ZMod 3) ^ 2 = 1 := rfl
    rw [this, one_pow, one_mul]
  rw [h2f] at h_zmod
  have h_mod : f % 2 < 2 := Nat.mod_lt _ (by decide)
  interval_cases hf_mod : f % 2 <;> revert h_zmod <;> decide

lemma pow_three_helper_999 (k : ℕ) : (3 : ZMod 999) ^ (18 * k + 3) = (3 : ZMod 999) ^ 3 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have : 18 * (k + 1) + 3 = 18 * k + 3 + 18 := by omega
    rw [this, pow_add, ih]
    rfl

lemma pow_three_zmod_999 (f : ℕ) (hf : f ≥ 3) :
    (3 : ZMod 999) ^ f = (3 : ZMod 999) ^ ((f - 3) % 18 + 3) := by
  have h_eq : f = 18 * ((f - 3) / 18) + 3 + (f - 3) % 18 := by omega
  conv_lhs => rw [h_eq]
  rw [pow_add, pow_three_helper_999, ← pow_add]
  have : 3 + (f - 3) % 18 = (f - 3) % 18 + 3 := by omega
  rw [this]

lemma pow_seven_zmod_999 (e : ℕ) (he : e ≥ 2) :
    (7 : ZMod 999) ^ e = (7 : ZMod 999) ^ ((e - 2) % 9 + 2) := by
  have h_eq : e = 9 * ((e - 2) / 9) + ((e - 2) % 9 + 2) := by omega
  conv_lhs => rw [h_eq]
  rw [pow_add, pow_mul]
  have : (7 : ZMod 999) ^ 9 = 1 := by rfl
  rw [this, one_pow, one_mul]

lemma pillai_diff_two_7_3 (e f : ℕ) (he : 1 < e) (hf : 1 < f) (h : 3 ^ f - 7 ^ e = 2) : False := by
  have hf3 : f ≥ 3 := by
    by_contra hc
    have : f = 2 := by omega
    subst this
    have : 3 ^ 2 - 7 ^ e = 2 := h
    have h_pow : 7 ^ e ≥ 49 := Nat.pow_le_pow_right (show 0 < 7 by decide) he
    omega
  have he2 : e ≥ 2 := he
  have h_zmod : (3 : ZMod 999) ^ f - (7 : ZMod 999) ^ e = 2 := by
    have h_ge : 3 ^ f ≥ 7 ^ e := by omega
    have h_cast : ((3 ^ f - 7 ^ e : ℕ) : ZMod 999) = ((2 : ℕ) : ZMod 999) := congrArg Nat.cast h
    rw [Nat.cast_sub h_ge] at h_cast
    push_cast at h_cast
    exact h_cast
  rw [pow_three_zmod_999 f hf3, pow_seven_zmod_999 e he2] at h_zmod
  have h_mod_f : (f - 3) % 18 < 18 := Nat.mod_lt _ (by decide)
  have h_mod_e : (e - 2) % 9 < 9 := Nat.mod_lt _ (by decide)
  interval_cases hf_mod : (f - 3) % 18 <;> interval_cases he_mod : (e - 2) % 9 <;> revert h_zmod <;> decide

lemma pillai_diff_two_3_11 (e f : ℕ) (he : 1 < e) (hf : 1 < f) (h : 11 ^ f - 3 ^ e = 2) : False := by
  have he2 : e ≥ 2 := he
  have h_zmod : (11 : ZMod 121) ^ f - (3 : ZMod 121) ^ e = 2 := by
    have h_ge : 11 ^ f ≥ 3 ^ e := by omega
    have h_cast : ((11 ^ f - 3 ^ e : ℕ) : ZMod 121) = ((2 : ℕ) : ZMod 121) := congrArg Nat.cast h
    rw [Nat.cast_sub h_ge] at h_cast
    push_cast at h_cast
    exact h_cast
  have h11f : (11 : ZMod 121) ^ f = 0 := by
    have hf_eq : f = (f - 2) + 2 := by omega
    rw [hf_eq, pow_add]
    have : (11 : ZMod 121) ^ 2 = 0 := by rfl
    rw [this, mul_zero]
  rw [h11f, zero_sub] at h_zmod
  have h_cast2 : (3 : ZMod 121) ^ e = 119 := by
    calc (3 : ZMod 121) ^ e = - (- (3 : ZMod 121) ^ e) := by ring
    _ = -2 := by rw [h_zmod]
    _ = 119 := rfl
  have h3e : (3 : ZMod 121) ^ e = (3 : ZMod 121) ^ (e % 110) := by
    have h_eq : e = 110 * (e / 110) + e % 110 := (Nat.div_add_mod e 110).symm
    conv_lhs => rw [h_eq]
    rw [pow_add, pow_mul]
    have : (3 : ZMod 121) ^ 110 = 1 := by rfl
    rw [this, one_pow, one_mul]
  rw [h3e] at h_cast2
  have h_mod : e % 110 < 110 := Nat.mod_lt _ (by decide)
  interval_cases he_mod : e % 110 <;> revert h_cast2 <;> decide

lemma pow_seven_helper_252 (k : ℕ) : (7 : ZMod 252) ^ (6 * k + 2) = (7 : ZMod 252) ^ 2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have : 6 * (k + 1) + 2 = 6 * k + 2 + 6 := by omega
    rw [this, pow_add, ih]
    rfl

lemma pow_seven_zmod_252 (e : ℕ) (he : e ≥ 2) :
    (7 : ZMod 252) ^ e = (7 : ZMod 252) ^ ((e - 2) % 6 + 2) := by
  have h_eq : e = 6 * ((e - 2) / 6) + 2 + (e - 2) % 6 := by omega
  conv_lhs => rw [h_eq]
  rw [pow_add, pow_seven_helper_252, ← pow_add]
  have : 2 + (e - 2) % 6 = (e - 2) % 6 + 2 := by omega
  rw [this]



-- Helper Lemmas


lemma odd_sq_mod_eight (y : ℕ) (hy : y % 2 = 1) : 8 ∣ y ^ 2 - 1 := by
  have h_mod : y % 8 < 8 := Nat.mod_lt _ (by decide)
  set k := y / 8
  interval_cases y_mod : y % 8
  · have : y % 2 = 0 := by
      have : y = 8 * k + 0 := by omega
      omega
    omega
  · have h_eq : y = 8 * k + 1 := by omega
    have h_sq : y ^ 2 = 8 * (8 * k ^ 2 + 2 * k) + 1 := by
      rw [h_eq]
      ring
    rw [h_sq]
    have : 8 * (8 * k ^ 2 + 2 * k) + 1 - 1 = 8 * (8 * k ^ 2 + 2 * k) := by omega
    rw [this]
    exact dvd_mul_right 8 _
  · have : y % 2 = 0 := by
      have : y = 8 * k + 2 := by omega
      omega
    omega
  · have h_eq : y = 8 * k + 3 := by omega
    have h_sq : y ^ 2 = 8 * (8 * k ^ 2 + 6 * k + 1) + 1 := by
      rw [h_eq]
      ring
    rw [h_sq]
    have : 8 * (8 * k ^ 2 + 6 * k + 1) + 1 - 1 = 8 * (8 * k ^ 2 + 6 * k + 1) := by omega
    rw [this]
    exact dvd_mul_right 8 _
  · have : y % 2 = 0 := by
      have : y = 8 * k + 4 := by omega
      omega
    omega
  · have h_eq : y = 8 * k + 5 := by omega
    have h_sq : y ^ 2 = 8 * (8 * k ^ 2 + 10 * k + 3) + 1 := by
      rw [h_eq]
      ring
    rw [h_sq]
    have : 8 * (8 * k ^ 2 + 10 * k + 3) + 1 - 1 = 8 * (8 * k ^ 2 + 10 * k + 3) := by omega
    rw [this]
    exact dvd_mul_right 8 _
  · have : y % 2 = 0 := by
      have : y = 8 * k + 6 := by omega
      omega
    omega
  · have h_eq : y = 8 * k + 7 := by omega
    have h_sq : y ^ 2 = 8 * (8 * k ^ 2 + 14 * k + 6) + 1 := by
      rw [h_eq]
      ring
    rw [h_sq]
    have : 8 * (8 * k ^ 2 + 14 * k + 6) + 1 - 1 = 8 * (8 * k ^ 2 + 14 * k + 6) := by omega
    rw [this]
    exact dvd_mul_right 8 _

lemma pow_five_zmod_eight (e : ℕ) : (5 : ZMod 8) ^ e = 1 ∨ (5 : ZMod 8) ^ e = 5 := by
  induction e with
  | zero => left; rfl
  | succ e ih =>
    rcases ih with h1 | h2
    · right; rw [pow_succ, h1, one_mul]
    · left; rw [pow_succ, h2]
      decide

lemma hy_odd_proof (q f : ℕ) (hq : Nat.Prime q) (hq_ne_2 : q ≠ 2) (hf : f % 2 = 0) (hf_pos : f > 0) :
    (q ^ (f / 2)) % 2 = 1 := by
  set y := q ^ (f / 2)
  by_contra hc
  have hc_even : y % 2 = 0 := by omega
  have h_even_y : 2 ∣ y := Nat.dvd_of_mod_eq_zero hc_even
  have h_even_q : 2 ∣ q := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h_even_y
  rcases hq.eq_one_or_self_of_dvd 2 h_even_q with h1 | h2
  · contradiction
  · exact hq_ne_2 h2.symm

lemma f_even_contradiction (e f q : ℕ) (hq : Nat.Prime q) (hq_ne_2 : q ≠ 2) (h_sq : q ^ f = 5 ^ e + 2) (hf_even : f % 2 = 0) (hf_pos : f > 0) : False := by
  have hf_eq : f = (f / 2) * 2 := by omega
  set y := q ^ (f / 2)
  have h_fy : q ^ f = y ^ 2 := by
    rw [hf_eq, pow_mul]
  have h_sq_y : y ^ 2 = 5 ^ e + 2 := by
    rw [← h_fy, h_sq]
  have hy_odd : y % 2 = 1 := hy_odd_proof q f hq hq_ne_2 hf_even hf_pos
  have h_dvd : 8 ∣ y ^ 2 - 1 := odd_sq_mod_eight y hy_odd
  have h_dvd_five : 8 ∣ 5 ^ e + 1 := by
    have h_sub : y ^ 2 - 1 = 5 ^ e + 1 := by
      generalize 5 ^ e = V at h_sq_y ⊢
      rw [h_sq_y]
      omega
    rw [h_sub] at h_dvd
    exact h_dvd
  have h_cast : ((5 ^ e + 1 : ℕ) : ZMod 8) = 0 := by
    rcases h_dvd_five with ⟨c, hc⟩
    have hc_cast : ((5 ^ e + 1 : ℕ) : ZMod 8) = ((8 * c : ℕ) : ZMod 8) := congrArg Nat.cast hc
    rw [hc_cast]
    push_cast
    have : (8 : ZMod 8) = 0 := rfl
    rw [this, zero_mul]
  have h_five_zmod : (5 : ZMod 8) ^ e = -1 := by
    have h_cast_push : (5 : ZMod 8) ^ e + 1 = 0 := by
      calc (5 : ZMod 8) ^ e + 1 = ((5 ^ e + 1 : ℕ) : ZMod 8) := by push_cast; rfl
      _ = 0 := h_cast
    calc (5 : ZMod 8) ^ e = (5 : ZMod 8) ^ e + 1 - 1 := by ring
    _ = 0 - 1 := by rw [h_cast_push]
    _ = -1 := by ring
  have h_pow_cases := pow_five_zmod_eight e
  rcases h_pow_cases with h1 | h2
  · rw [h1] at h_five_zmod
    have : (1 : ZMod 8) = -1 := h_five_zmod
    revert this
    decide
  · rw [h2] at h_five_zmod
    have : (5 : ZMod 8) = -1 := h_five_zmod
    revert this
    decide

lemma pow_two_zmod_three_odd (e : ℕ) (he_odd : e % 2 = 1) : (2 : ZMod 3) ^ e = 2 := by
  have h_eq : e = 2 * (e / 2) + 1 := by omega
  rw [h_eq]
  have : (2 : ZMod 3) ^ (2 * (e / 2) + 1) = ((2 : ZMod 3) ^ 2) ^ (e / 2) * 2 := by
    rw [pow_succ, pow_mul]
  rw [this]
  have : (2 : ZMod 3) ^ 2 = 1 := rfl
  rw [this, one_pow, one_mul]

lemma q_mod_3_contradiction (e f q : ℕ) (hq_mod : q % 3 = 2) (he_odd : e % 2 = 1) (h : q ^ f = 5 ^ e + 2) : f % 2 = 0 := by
  by_contra hf_odd_hc
  have hf_odd : f % 2 = 1 := by omega
  have h_cast : ((q ^ f : ℕ) : ZMod 3) = ((5 ^ e + 2 : ℕ) : ZMod 3) := congrArg Nat.cast h
  push_cast at h_cast
  have hq_cast : (q : ZMod 3) = 2 := by
    have : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
    rw [this, hq_mod]
    rfl
  have h5_cast : (5 : ZMod 3) = 2 := rfl
  rw [hq_cast, h5_cast] at h_cast
  have hq_pow : (2 : ZMod 3) ^ f = 2 := pow_two_zmod_three_odd f hf_odd
  have h5_pow : (2 : ZMod 3) ^ e = 2 := pow_two_zmod_three_odd e he_odd
  rw [hq_pow, h5_pow] at h_cast
  have : (2 : ZMod 3) = 2 + 2 := h_cast
  revert this
  decide

lemma dvd_contradiction_eight (q : ℕ) (hq : Nat.Prime q) (hq_ne_2 : q ≠ 2) (h_dvd : 8 ∣ q) : False := by
  have : 2 ∣ q := dvd_trans (by decide) h_dvd
  rcases hq.eq_one_or_self_of_dvd 2 this with h1 | h2
  · contradiction
  · exact hq_ne_2 h2.symm

lemma dvd_contradiction_25 (q : ℕ) (hq : Nat.Prime q) (hq5_val : q % 5 = 2) (h_dvd : 25 ∣ q) : False := by
  have : 5 ∣ q := dvd_trans (by decide) h_dvd
  rcases hq.eq_one_or_self_of_dvd 5 this with h1 | h2
  · contradiction
  · subst h2
    revert hq5_val
    decide

lemma mod_two_eq_zero_of_mod_eight_eq_two (n : ℕ) (h : n % 8 = 2) : n % 2 = 0 := by omega
lemma mod_two_eq_zero_of_mod_eight_eq_four (n : ℕ) (h : n % 8 = 4) : n % 2 = 0 := by omega
lemma mod_two_eq_zero_of_mod_eight_eq_six (n : ℕ) (h : n % 8 = 6) : n % 2 = 0 := by omega

lemma non_coprime_contradiction (q M g r : ℕ) (hq_coprime : Nat.Coprime q M) 
    (h_g_dvd_M : g ∣ M) (h_g_dvd_r : g ∣ r) (hq_mod : q % M = r) (hg : 1 < g) : False := by
  have h_g_dvd_q : g ∣ q := by
    have : q = M * (q / M) + r := (Nat.div_add_mod q M).symm.trans (by omega)
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_M (q / M)) h_g_dvd_r
  have h_g_dvd_gcd : g ∣ q.gcd M := Nat.dvd_gcd h_g_dvd_q h_g_dvd_M
  have h_gcd : q.gcd M = 1 := hq_coprime
  rw [h_gcd] at h_g_dvd_gcd
  have : g ≤ 1 := Nat.le_of_dvd (by decide) h_g_dvd_gcd
  omega

lemma pow_three_zmod_29 (e : ℕ) : (3 : ZMod 29) ^ e = 27 ↔ e % 28 = 3 := by
  have h_eq : e = 28 * (e / 28) + e % 28 := (Nat.div_add_mod e 28).symm
  have h_pow : (3 : ZMod 29) ^ e = (3 : ZMod 29) ^ (e % 28) := by
    conv_lhs => rw [h_eq]
    rw [pow_add, pow_mul]
    have : (3 : ZMod 29) ^ 28 = 1 := by decide
    rw [this, one_pow, one_mul]
  rw [h_pow]
  have h_mod : e % 28 < 28 := Nat.mod_lt _ (by decide)
  interval_cases h_cases : e % 28 <;> decide

lemma pow_three_zmod_83 (e : ℕ) : (3 : ZMod 83) ^ e = 81 ↔ e % 41 = 4 := by
  have h_eq : e = 41 * (e / 41) + e % 41 := (Nat.div_add_mod e 41).symm
  have h_pow : (3 : ZMod 83) ^ e = (3 : ZMod 83) ^ (e % 41) := by
    conv_lhs => rw [h_eq]
    rw [pow_add, pow_mul]
    have : (3 : ZMod 83) ^ 41 = 1 := by decide
    rw [this, one_pow, one_mul]
  rw [h_pow]
  have h_mod : e % 41 < 41 := Nat.mod_lt _ (by decide)
  interval_cases h_cases : e % 41 <;> decide

def NoSol (M phi r : ℕ) : Prop :=
  ∀ f_mod < phi, ∀ e_mod < 6, (r : ZMod M) ^ f_mod - (3 : ZMod M) ^ (e_mod + 2) ≠ 2

instance (M phi r : ℕ) : Decidable (NoSol M phi r) := by
  dsimp [NoSol]
  infer_instance

lemma zmod_cast_of_dvd (q M N r : ℕ) (h_dvd : N ∣ M) (hq_mod : q % M = r) :
    (q : ZMod N) = ((r % N : ℕ) : ZMod N) := by
  have h_eq : q = M * (q / M) + r := by
    have := (Nat.div_add_mod q M).symm
    rw [hq_mod] at this
    exact this
  have h_cast : (q : ZMod N) = ((M * (q / M) + r : ℕ) : ZMod N) := congrArg Nat.cast h_eq
  rw [h_cast]
  push_cast
  rcases h_dvd with ⟨k, rfl⟩
  have h_mul_zero : ((N * k : ℕ) : ZMod N) = 0 := by
    push_cast
    rw [ZMod.natCast_self, zero_mul]
  rw [h_mul_zero, zero_mul, zero_add]
  have h_mod : ((r : ℕ) : ZMod N) = ((r % N : ℕ) : ZMod N) := by
    nth_rw 1 [← Nat.div_add_mod r N]
    push_cast
    rw [ZMod.natCast_self, zero_mul, zero_add]
  exact h_mod

lemma zmod_equation (p q e f M : ℕ) (h : q ^ f - p ^ e = 2) :
    (q : ZMod M) ^ f - (p : ZMod M) ^ e = 2 := by
  have h_ge : q ^ f ≥ p ^ e := by omega
  have h_cast : ((q ^ f - p ^ e : ℕ) : ZMod M) = ((2 : ℕ) : ZMod M) := congrArg Nat.cast h
  rw [Nat.cast_sub h_ge] at h_cast
  push_cast at h_cast
  exact h_cast

lemma pow_mod_period (B : ZMod M) (f P : ℕ) (hP : B ^ P = 1) :
    B ^ f = B ^ (f % P) := by
  have h_eq : f = P * (f / P) + f % P := (Nat.div_add_mod f P).symm
  conv_lhs => rw [h_eq]
  rw [pow_add, pow_mul, hP, one_pow, one_mul]

lemma pow_three_period (e M : ℕ) (he : 1 < e) (h_decide : (3 : ZMod M) ^ 6 * 9 = 9) :
    (3 : ZMod M) ^ e = (3 : ZMod M) ^ ((e - 2) % 6 + 2) := by
  have h_eq : e = 6 * ((e - 2) / 6) + ((e - 2) % 6 + 2) := by omega
  conv_lhs => rw [h_eq]
  rw [pow_add]
  have h_eq2 : (3 : ZMod M) ^ ((e - 2) % 6 + 2) = 9 * (3 : ZMod M) ^ ((e - 2) % 6) := by
    have : (e - 2) % 6 + 2 = 2 + (e - 2) % 6 := by omega
    rw [this, pow_add]
    have : (3 : ZMod M) ^ 2 = 9 := by ring
    rw [this]
  rw [h_eq2]
  have h_assoc : (3 : ZMod M) ^ (6 * ((e - 2) / 6)) * (9 * 3 ^ ((e - 2) % 6)) =
      ((3 : ZMod M) ^ (6 * ((e - 2) / 6)) * 9) * 3 ^ ((e - 2) % 6) := by ring
  rw [h_assoc]
  have pow_three_helper : ∀ k : ℕ, (3 : ZMod M) ^ (6 * k) * 9 = 9 := by
    intro k
    induction k with
    | zero => simp only [mul_zero, pow_zero, one_mul]
    | succ k ih =>
      have h_step : 6 * (k + 1) = 6 * k + 6 := by ring
      rw [h_step, pow_add]
      have h_assoc2 : (3 : ZMod M) ^ (6 * k) * 3 ^ 6 * 9 = (3 : ZMod M) ^ (6 * k) * (3 ^ 6 * 9) := by ring
      rw [h_assoc2, h_decide, ih]
  rw [pow_three_helper, ← h_eq2]

lemma no_sol_contradiction (M phi r f e : ℕ) (phi_pos : 0 < phi)
    (h_zmod : (r : ZMod M) ^ (f % phi) - (3 : ZMod M) ^ ((e - 2) % 6 + 2) = 2)
    (h_no_sol : NoSol M phi r) : False := by
  have hf_mod : f % phi < phi := Nat.mod_lt _ phi_pos
  have he_mod : (e - 2) % 6 < 6 := Nat.mod_lt _ (by decide)
  exact h_no_sol (f % phi) hf_mod ((e - 2) % 6) he_mod h_zmod

lemma zmod_cast_8 (p r : ℕ) (h : p % 8 = r) : (p : ZMod 8) = (r : ZMod 8) := by
  have h_cast : ((p : ℕ) : ZMod 8) = ((p % 8 : ℕ) : ZMod 8) := by rw [ZMod.natCast_mod]
  rw [h_cast, h]

lemma lt_cases_exception (q e f E_val R_val M_val : ℕ) (hq_ge : q ≥ M_val) (he_ge : e ≥ 3) (he_ne : e ≠ E_val) (hf : f > 0)
    (h_eq : q ^ f = 3 ^ e + 2) (h_lt : 3 ^ (E_val - 1) + 2 < M_val) (h_E : E_val ≥ 3) : e ≥ E_val + 1 := by
  by_contra hc
  have he_lt : e < E_val := by omega
  have he_le : e ≤ E_val - 1 := by omega
  have h_pow : 3 ^ e + 2 ≤ 3 ^ (E_val - 1) + 2 := by
    have : 3 ^ e ≤ 3 ^ (E_val - 1) := Nat.pow_le_pow_right (by decide) he_le
    omega
  have : q ^ f < M_val := by
    calc q ^ f = 3 ^ e + 2 := h_eq
    _ ≤ 3 ^ (E_val - 1) + 2 := h_pow
    _ < M_val := h_lt
  have : q ^ f ≥ M_val := by
    calc q ^ f ≥ q ^ 1 := Nat.pow_le_pow_right (by omega) hf
    _ = q := pow_one q
    _ ≥ M_val := hq_ge
  omega


lemma pillai_diff_two (p q e f : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (he : 1 < e) (hf : 1 < f) (h : q ^ f - p ^ e = 2) :
    p = 5 ∧ e = 2 ∧ q = 3 ∧ f = 3 := by
  by_cases hlt : p ^ e < 27
  · exact pillai_diff_two_lt_27 p q e f hp hq he hf h hlt
  · exfalso
    have hp_ne_2 : p ≠ 2 := p_ne_two p q e f hp hq he hf h
    have hq_ne_2 : q ≠ 2 := q_ne_two p q e f hp hq he hf h
    have hp_cases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p ≥ 11 := by
      have : p ≠ 0 := hp.ne_zero
      have : p ≠ 1 := hp.ne_one
      have : p ≠ 4 := by intro hc; subst hc; revert hp; decide
      have : p ≠ 6 := by intro hc; subst hc; revert hp; decide
      have : p ≠ 8 := by intro hc; subst hc; revert hp; decide
      have : p ≠ 9 := by intro hc; subst hc; revert hp; decide
      have : p ≠ 10 := by intro hc; subst hc; revert hp; decide
      omega
    have hq_cases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q ≥ 11 := by
      have : q ≠ 0 := hq.ne_zero
      have : q ≠ 1 := hq.ne_one
      have : q ≠ 4 := by intro hc; subst hc; revert hq; decide
      have : q ≠ 6 := by intro hc; subst hc; revert hq; decide
      have : q ≠ 8 := by intro hc; subst hc; revert hq; decide
      have : q ≠ 9 := by intro hc; subst hc; revert hq; decide
      have : q ≠ 10 := by intro hc; subst hc; revert hq; decide
      omega
    rcases hp_cases with rfl | rfl | rfl | rfl | hp_ge11
    · contradiction
    · -- p = 3
      have he3 : e ≥ 3 := by
        by_contra hc
        have : e = 2 := by omega
        subst this
        have : 3 ^ 2 < 27 := by decide
        omega
      rcases hq_cases with rfl | rfl | rfl | rfl | hq_ge11
      · contradiction
      · exact (q_ne_p_of_diff_two 3 3 e f hp he h rfl).elim
      · exact pillai_diff_two_3_5 e f (by omega) hf h
      · exact pillai_diff_two_3_7 e f (by omega) h
      · -- q >= 11
        by_cases hq11 : q = 11
        · subst hq11
          exact pillai_diff_two_3_11 e f (by omega) hf h
        by_cases hq23 : q = 23
        · subst hq23
          by_contra
          have h_zmod : (23 : ZMod 11) ^ f - (3 : ZMod 11) ^ e = 2 := by
            have h_ge : 23 ^ f ≥ 3 ^ e := by
              by_contra hc
              have : 23 ^ f - 3 ^ e = 0 := Nat.sub_eq_zero_of_le (by omega)
              omega
            have h_cast : ((23 ^ f - 3 ^ e : ℕ) : ZMod 11) = ((2 : ℕ) : ZMod 11) := congrArg Nat.cast h
            rw [Nat.cast_sub h_ge] at h_cast
            push_cast at h_cast
            exact h_cast
          have h23 : (23 : ZMod 11) = 1 := rfl
          rw [h23, one_pow] at h_zmod
          have h_cast2 : (3 : ZMod 11) ^ e = 10 := by
            calc (3 : ZMod 11) ^ e = 1 - ((1 : ZMod 11) - (3 : ZMod 11) ^ e) := by ring
            _ = 1 - 2 := by rw [h_zmod]
            _ = 10 := rfl
          have h3e : (3 : ZMod 11) ^ e = (3 : ZMod 11) ^ (e % 5) := by
            have h_eq : e = 5 * (e / 5) + e % 5 := (Nat.div_add_mod e 5).symm
            conv_lhs => rw [h_eq]
            rw [pow_add, pow_mul]
            have : (3 : ZMod 11) ^ 5 = 1 := by decide
            rw [this, one_pow, one_mul]
          rw [h3e] at h_cast2
          have h_mod : e % 5 < 5 := Nat.mod_lt _ (by decide)
          interval_cases he_mod : e % 5 <;> revert h_cast2 <;> decide
        by_cases hq29 : q = 29
        · subst hq29
          by_contra
          by_cases he3 : e = 3
          · subst he3
            have h_eq : 29 ^ f = 29 := by omega
            have h_lt : f < 2 := by
              by_contra hc
              have h_ge : f ≥ 2 := by omega
              have : 29 ^ f ≥ 841 := by
                calc 29 ^ f ≥ 29 ^ 2 := Nat.pow_le_pow_right (by decide) h_ge
                _ = 841 := by decide
              omega
            have h_f_pos : f > 0 := by
              by_contra hc
              have : f = 0 := by omega
              subst this
              omega
            have : f = 1 := by omega
            omega
          · have he4 : e ≥ 4 := by omega
            have h_zmod : (29 : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := by
              have h_ge : 29 ^ f ≥ 3 ^ e := by
                by_contra hc
                have : 29 ^ f - 3 ^ e = 0 := Nat.sub_eq_zero_of_le (by omega)
                omega
              have h_cast : ((29 ^ f - 3 ^ e : ℕ) : ZMod 9) = ((2 : ℕ) : ZMod 9) := congrArg Nat.cast h
              rw [Nat.cast_sub h_ge] at h_cast
              push_cast at h_cast
              exact h_cast
            have h3e : (3 : ZMod 9) ^ e = 0 := by
              have he_eq : e = (e - 4) + 4 := by omega
              rw [he_eq, pow_add]
              have : (3 : ZMod 9) ^ 4 = 0 := rfl
              rw [this, mul_zero]
            rw [h3e, sub_zero] at h_zmod
            have h29f : (29 : ZMod 9) ^ f = (2 : ZMod 9) ^ f := rfl
            rw [h29f] at h_zmod
            have h2f : (2 : ZMod 9) ^ f = (2 : ZMod 9) ^ (f % 6) := by
              have h_eq : f = 6 * (f / 6) + f % 6 := (Nat.div_add_mod f 6).symm
              conv_lhs => rw [h_eq]
              rw [pow_add, pow_mul]
              have : (2 : ZMod 9) ^ 6 = 1 := by decide
              rw [this, one_pow, one_mul]
            rw [h2f] at h_zmod
            have hf_mod : f % 6 < 6 := Nat.mod_lt _ (by decide)
            interval_cases hf_mod_val : f % 6 <;> revert h_zmod <;> decide
        by_cases hq83 : q = 83
        · subst hq83
          by_contra
          by_cases he4 : e = 4
          · subst he4
            have h_eq : 83 ^ f = 83 := by omega
            have h_lt : f < 2 := by
              by_contra hc
              have h_ge : f ≥ 2 := by omega
              have : 83 ^ f ≥ 6889 := by
                calc 83 ^ f ≥ 83 ^ 2 := Nat.pow_le_pow_right (by decide) h_ge
                _ = 6889 := by decide
              omega
            have h_f_pos : f > 0 := by
              by_contra hc
              have : f = 0 := by omega
              subst this
              omega
            have : f = 1 := by omega
            omega
          · have he5 : e ≥ 5 := by omega
            have h_zmod : (83 : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := by
              have h_ge : 83 ^ f ≥ 3 ^ e := by
                by_contra hc
                have : 83 ^ f - 3 ^ e = 0 := Nat.sub_eq_zero_of_le (by omega)
                omega
              have h_cast : ((83 ^ f - 3 ^ e : ℕ) : ZMod 9) = ((2 : ℕ) : ZMod 9) := congrArg Nat.cast h
              rw [Nat.cast_sub h_ge] at h_cast
              push_cast at h_cast
              exact h_cast
            have h3e : (3 : ZMod 9) ^ e = 0 := by
              have he_eq : e = (e - 5) + 5 := by omega
              rw [he_eq, pow_add]
              have : (3 : ZMod 9) ^ 5 = 0 := rfl
              rw [this, mul_zero]
            rw [h3e, sub_zero] at h_zmod
            have h83f : (83 : ZMod 9) ^ f = (2 : ZMod 9) ^ f := rfl
            rw [h83f] at h_zmod
            have h2f : (2 : ZMod 9) ^ f = (2 : ZMod 9) ^ (f % 6) := by
              have h_eq : f = 6 * (f / 6) + f % 6 := (Nat.div_add_mod f 6).symm
              conv_lhs => rw [h_eq]
              rw [pow_add, pow_mul]
              have : (2 : ZMod 9) ^ 6 = 1 := by decide
              rw [this, one_pow, one_mul]
            rw [h2f] at h_zmod
            have hf_mod : f % 6 < 6 := Nat.mod_lt _ (by decide)
            interval_cases hf_mod_val : f % 6 <;> revert h_zmod <;> decide
        by_cases hq113 : q = 113
        · subst hq113
          by_contra
          have h_zmod113 : (3 : ZMod 113) ^ e = 111 := by
            have h_ge : 113 ^ f ≥ 3 ^ e := by
              by_contra hc
              have : 113 ^ f - 3 ^ e = 0 := Nat.sub_eq_zero_of_le (by omega)
              omega
            have h_cast : ((113 ^ f - 3 ^ e : ℕ) : ZMod 113) = ((2 : ℕ) : ZMod 113) := congrArg Nat.cast h
            rw [Nat.cast_sub h_ge] at h_cast
            push_cast at h_cast
            have h113f : (113 : ZMod 113) ^ f = 0 := by
              have hf_eq : f = (f - 2) + 2 := by omega
              rw [hf_eq, pow_add]
              have : (113 : ZMod 113) ^ 2 = 0 := rfl
              rw [this, mul_zero]
            rw [h113f, zero_sub] at h_cast
            calc (3 : ZMod 113) ^ e = - (- (3 : ZMod 113) ^ e) := by ring
            _ = -2 := by rw [h_cast]
            _ = 111 := rfl
          have h3e_113 : (3 : ZMod 113) ^ e = (3 : ZMod 113) ^ (e % 112) := by
            have h_eq : e = 112 * (e / 112) + e % 112 := (Nat.div_add_mod e 112).symm
            conv_lhs => rw [h_eq]
            rw [pow_add, pow_mul]
            have : (3 : ZMod 113) ^ 112 = 1 := by decide
            rw [this, one_pow, one_mul]
          rw [h3e_113] at h_zmod113
          have he_mod : e % 112 = 68 := by
            have h_mod_lt : e % 112 < 112 := Nat.mod_lt _ (by decide)
            interval_cases h_cases : e % 112 <;> revert h_zmod113 <;> decide
          have he_mod4 : e % 4 = 0 := by
            have h_div : e = 112 * (e / 112) + 68 := by
              have := Nat.div_add_mod e 112
              rw [he_mod] at this
              exact this.symm
            rw [h_div]
            omega
          have h_zmod8 : (113 : ZMod 8) ^ f - (3 : ZMod 8) ^ e = 2 := by
            have h_ge : 113 ^ f ≥ 3 ^ e := by
              by_contra hc
              have : 113 ^ f - 3 ^ e = 0 := Nat.sub_eq_zero_of_le (by omega)
              omega
            have h_cast : ((113 ^ f - 3 ^ e : ℕ) : ZMod 8) = ((2 : ℕ) : ZMod 8) := congrArg Nat.cast h
            rw [Nat.cast_sub h_ge] at h_cast
            push_cast at h_cast
            exact h_cast
          have h113_8 : (113 : ZMod 8) = 1 := rfl
          have h3e_8 : (3 : ZMod 8) ^ e = 1 := by
            have h_eq : e = 4 * (e / 4) + e % 4 := (Nat.div_add_mod e 4).symm
            conv_lhs => rw [h_eq]
            rw [pow_add, pow_mul, he_mod4]
            have : (3 : ZMod 8) ^ 4 = 1 := by decide
            rw [this, one_pow, one_mul]
            rfl
          rw [h113_8, one_pow, h3e_8] at h_zmod8
          revert h_zmod8; decide
        by_cases hq131 : q = 131
        · subst hq131
          by_contra
          have h_zmod : (131 : ZMod 11) ^ f - (3 : ZMod 11) ^ e = 2 := by
            have h_ge : 131 ^ f ≥ 3 ^ e := by
              by_contra hc
              have : 131 ^ f - 3 ^ e = 0 := Nat.sub_eq_zero_of_le (by omega)
              omega
            have h_cast : ((131 ^ f - 3 ^ e : ℕ) : ZMod 11) = ((2 : ℕ) : ZMod 11) := congrArg Nat.cast h
            rw [Nat.cast_sub h_ge] at h_cast
            push_cast at h_cast
            exact h_cast
          have h131 : (131 : ZMod 11) = -1 := rfl
          have h3e : (3 : ZMod 11) ^ e = (3 : ZMod 11) ^ (e % 5) := by
            have h_eq : e = 5 * (e / 5) + e % 5 := (Nat.div_add_mod e 5).symm
            conv_lhs => rw [h_eq]
            rw [pow_add, pow_mul]
            have : (3 : ZMod 11) ^ 5 = 1 := by decide
            rw [this, one_pow, one_mul]
          rw [h131, h3e] at h_zmod
          have hqf : (-1 : ZMod 11) ^ f = (-1 : ZMod 11) ^ (f % 2) := by
            have h_eq : f = 2 * (f / 2) + f % 2 := (Nat.div_add_mod f 2).symm
            conv_lhs => rw [h_eq]
            rw [pow_add, pow_mul]
            have : (-1 : ZMod 11) ^ 2 = 1 := rfl
            rw [this, one_pow, one_mul]
          rw [hqf] at h_zmod
          have h_mod_f : f % 2 < 2 := Nat.mod_lt _ (by decide)
          have h_mod_e : e % 5 < 5 := Nat.mod_lt _ (by decide)
          interval_cases h_cases_f : f % 2 <;> interval_cases h_cases_e : e % 5 <;> revert h_zmod <;> decide
        by_cases hq167 : q = 167
        · subst hq167
          by_contra
          have h_zmod : (167 : ZMod 83) ^ f - (3 : ZMod 83) ^ e = 2 := by
            have h_ge : 167 ^ f ≥ 3 ^ e := by
              by_contra hc
              have : 167 ^ f - 3 ^ e = 0 := Nat.sub_eq_zero_of_le (by omega)
              omega
            have h_cast : ((167 ^ f - 3 ^ e : ℕ) : ZMod 83) = ((2 : ℕ) : ZMod 83) := congrArg Nat.cast h
            rw [Nat.cast_sub h_ge] at h_cast
            push_cast at h_cast
            exact h_cast
          have h167 : (167 : ZMod 83) = 1 := rfl
          rw [h167, one_pow] at h_zmod
          have h_cast2 : (3 : ZMod 83) ^ e = 82 := by
            calc (3 : ZMod 83) ^ e = 1 - ((1 : ZMod 83) - (3 : ZMod 83) ^ e) := by ring
            _ = 1 - 2 := by rw [h_zmod]
            _ = 82 := rfl
          have h3e : (3 : ZMod 83) ^ e = (3 : ZMod 83) ^ (e % 82) := by
            have h_eq : e = 82 * (e / 82) + e % 82 := (Nat.div_add_mod e 82).symm
            conv_lhs => rw [h_eq]
            rw [pow_add, pow_mul]
            have : (3 : ZMod 83) ^ 82 = 1 := by decide
            rw [this, one_pow, one_mul]
          rw [h3e] at h_cast2
          have h_mod : e % 82 < 82 := Nat.mod_lt _ (by decide)
          interval_cases he_mod : e % 82 <;> revert h_cast2 <;> decide
        by_cases hq173 : q = 173
        · subst hq173
          by_contra
          have he_even : e % 2 = 0 := by
            by_contra hc
            have he_odd : e % 2 = 1 := by omega
            have h_zmod : (173 : ZMod 5) ^ f - (3 : ZMod 5) ^ e = 2 := by
              have h_ge : 173 ^ f ≥ 3 ^ e := by
                by_contra hc
                have : 173 ^ f - 3 ^ e = 0 := Nat.sub_eq_zero_of_le (by omega)
                omega
              have h_cast : ((173 ^ f - 3 ^ e : ℕ) : ZMod 5) = ((2 : ℕ) : ZMod 5) := congrArg Nat.cast h
              rw [Nat.cast_sub h_ge] at h_cast
              push_cast at h_cast
              exact h_cast
            have h173 : (173 : ZMod 5) = 3 := rfl
            have hf_odd : f % 2 = 1 := by
              by_contra hc_f
              have hf_even : f % 2 = 0 := by omega
              have h_zmod_local : (173 : ZMod 3) ^ f - (3 : ZMod 3) ^ e = 2 := by
                have h_ge : 173 ^ f ≥ 3 ^ e := by
                  by_contra hc
                  have : 173 ^ f - 3 ^ e = 0 := Nat.sub_eq_zero_of_le (by omega)
                  omega
                have h_cast : ((173 ^ f - 3 ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h
                rw [Nat.cast_sub h_ge] at h_cast
                push_cast at h_cast
                exact h_cast
              have h173_3 : (173 : ZMod 3) = 2 := rfl
              have h3e_3 : (3 : ZMod 3) ^ e = 0 := by
                have he_eq : e = (e - 1) + 1 := by omega
                rw [he_eq, pow_succ]
                have : (3 : ZMod 3) = 0 := rfl
                rw [this, mul_zero]
              have hqf_3 : (2 : ZMod 3) ^ f = 1 := by
                have h_eq : f = 2 * (f / 2) := by omega
                rw [h_eq, pow_mul]
                have : (2 : ZMod 3) ^ 2 = 1 := rfl
                rw [this, one_pow]
              rw [h173_3] at h_zmod_local
              rw [hqf_3, h3e_3, sub_zero] at h_zmod_local
              revert h_zmod_local; decide
            have h173f_5 : (3 : ZMod 5) ^ f = (3 : ZMod 5) ^ (f % 4) := by
              have h_eq : f = 4 * (f / 4) + f % 4 := (Nat.div_add_mod f 4).symm
              conv_lhs => rw [h_eq]
              rw [pow_add, pow_mul]
              have : (3 : ZMod 5) ^ 4 = 1 := by decide
              rw [this, one_pow, one_mul]
            have h3e_5 : (3 : ZMod 5) ^ e = (3 : ZMod 5) ^ (e % 4) := by
              have h_eq : e = 4 * (e / 4) + e % 4 := (Nat.div_add_mod e 4).symm
              conv_lhs => rw [h_eq]
              rw [pow_add, pow_mul]
              have : (3 : ZMod 5) ^ 4 = 1 := by decide
              rw [this, one_pow, one_mul]
            rw [h173, h173f_5, h3e_5] at h_zmod
            have hf_mod : f % 4 < 4 := Nat.mod_lt _ (by decide)
            have he_mod : e % 4 < 4 := Nat.mod_lt _ (by decide)
            interval_cases hf_mod_val : f % 4 <;> interval_cases he_mod_val : e % 4 <;> revert h_zmod <;> decide
          have h_zmod8 : (173 : ZMod 8) ^ f - (3 : ZMod 8) ^ e = 2 := by
            have h_ge : 173 ^ f ≥ 3 ^ e := by
              by_contra hc
              have : 173 ^ f - 3 ^ e = 0 := Nat.sub_eq_zero_of_le (by omega)
              omega
            have h_cast : ((173 ^ f - 3 ^ e : ℕ) : ZMod 8) = ((2 : ℕ) : ZMod 8) := congrArg Nat.cast h
            rw [Nat.cast_sub h_ge] at h_cast
            push_cast at h_cast
            exact h_cast
          have h173_8 : (173 : ZMod 8) = 5 := rfl
          have hf_odd : f % 2 = 1 := by
            by_contra hc_f
            have hf_even : f % 2 = 0 := by omega
            have h_zmod_local : (173 : ZMod 3) ^ f - (3 : ZMod 3) ^ e = 2 := by
              have h_ge : 173 ^ f ≥ 3 ^ e := by
                by_contra hc
                have : 173 ^ f - 3 ^ e = 0 := Nat.sub_eq_zero_of_le (by omega)
                omega
              have h_cast : ((173 ^ f - 3 ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h
              rw [Nat.cast_sub h_ge] at h_cast
              push_cast at h_cast
              exact h_cast
            have h173_3 : (173 : ZMod 3) = 2 := rfl
            have h3e_3 : (3 : ZMod 3) ^ e = 0 := by
              have he_eq : e = (e - 1) + 1 := by omega
              rw [he_eq, pow_succ]
              have : (3 : ZMod 3) = 0 := rfl
              rw [this, mul_zero]
            have hqf_3 : (2 : ZMod 3) ^ f = 1 := by
              have h_eq : f = 2 * (f / 2) := by omega
              rw [h_eq, pow_mul]
              have : (2 : ZMod 3) ^ 2 = 1 := rfl
              rw [this, one_pow]
            rw [h173_3] at h_zmod_local
            rw [hqf_3, h3e_3, sub_zero] at h_zmod_local
            revert h_zmod_local; decide
          have hqf_8 : (5 : ZMod 8) ^ f = 5 := by
            have h_eq : f = 2 * (f / 2) + 1 := by omega
            rw [h_eq]
            have : (5 : ZMod 8) ^ (2 * (f / 2) + 1) = ((5 : ZMod 8) ^ 2) ^ (f / 2) * 5 := by rw [pow_succ, pow_mul]
            rw [this]
            have : (5 : ZMod 8) ^ 2 = 1 := rfl
            rw [this, one_pow, one_mul]
          have h3e_8 : (3 : ZMod 8) ^ e = 1 := by
            have h_eq : e = 2 * (e / 2) := by omega
            rw [h_eq, pow_mul]
            have : (3 : ZMod 8) ^ 2 = 1 := rfl
            rw [this, one_pow]
          rw [h173_8, hqf_8, h3e_8] at h_zmod8
          revert h_zmod8; decide
        by_cases hq227 : q = 227
        · subst hq227
          by_contra
          by_cases he5 : e = 5
          · subst he5
            have h_eq : 227 ^ f = 245 := by omega
            have h_lt : f < 2 := by
              by_contra hc
              have h_ge : f ≥ 2 := by omega
              have : 227 ^ f ≥ 51529 := by
                calc 227 ^ f ≥ 227 ^ 2 := Nat.pow_le_pow_right (by decide) h_ge
                _ = 51529 := by decide
              omega
            have h_f_pos : f > 0 := by
              by_contra hc
              have : f = 0 := by omega
              subst this
              omega
            have : f = 1 := by omega
            omega
          · have he6 : e ≥ 6 := by omega
            have h_zmod : (227 : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := by
              have h_ge : 227 ^ f ≥ 3 ^ e := by
                by_contra hc
                have : 227 ^ f - 3 ^ e = 0 := Nat.sub_eq_zero_of_le (by omega)
                omega
              have h_cast : ((227 ^ f - 3 ^ e : ℕ) : ZMod 9) = ((2 : ℕ) : ZMod 9) := congrArg Nat.cast h
              rw [Nat.cast_sub h_ge] at h_cast
              push_cast at h_cast
              exact h_cast
            have h3e : (3 : ZMod 9) ^ e = 0 := by
              have he_eq : e = (e - 6) + 6 := by omega
              rw [he_eq, pow_add]
              have : (3 : ZMod 9) ^ 6 = 0 := rfl
              rw [this, mul_zero]
            rw [h3e, sub_zero] at h_zmod
            have h227f : (227 : ZMod 9) ^ f = (2 : ZMod 9) ^ f := rfl
            rw [h227f] at h_zmod
            have h2f : (2 : ZMod 9) ^ f = (2 : ZMod 9) ^ (f % 6) := by
              have h_eq : f = 6 * (f / 6) + f % 6 := (Nat.div_add_mod f 6).symm
              conv_lhs => rw [h_eq]
              rw [pow_add, pow_mul]
              have : (2 : ZMod 9) ^ 6 = 1 := by decide
              rw [this, one_pow, one_mul]
            rw [h2f] at h_zmod
            have hf_mod : f % 6 < 6 := Nat.mod_lt _ (by decide)
            interval_cases hf_mod_val : f % 6 <;> revert h_zmod <;> decide
        have hq_ge13 : q ≥ 13 := by omega
        have hq_coprime : Nat.Coprime q 252 := (coprime_252_of_prime q hq hq_ne_2 (by omega) (by omega)).2
        have h_zmod : (q : ZMod 252) ^ f - (3 : ZMod 252) ^ e = 2 := by
          have h_ge : q ^ f ≥ 3 ^ e := by
            by_contra hc
            have : q ^ f - 3 ^ e = 0 := Nat.sub_eq_zero_of_le (by omega)
            omega
          have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 252) = ((2 : ℕ) : ZMod 252) := congrArg Nat.cast h
          rw [Nat.cast_sub h_ge] at h_cast
          push_cast at h_cast
          exact h_cast
        set r := q % 252
        have hr_lt : r < 252 := Nat.mod_lt q (by decide)
        have q_mod : q % 252 = r := rfl
        interval_cases r
        · exact non_coprime_contradiction q 252 252 0 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 1
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 1 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (1 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 1 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 2 2 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 3 3 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 4 4 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 5
          have h_zmod_M : (q : ZMod 252) ^ f - (3 : ZMod 252) ^ e = 2 := zmod_equation 3 q e f 252 h
          rw [zmod_cast_of_dvd q 252 252 5 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (5 : ZMod 252) f 72 (by decide)] at h_zmod_M
          rw [pow_three_period e 252 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 252 72 5 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 6 6 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 7 7 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 4 8 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 9 9 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 2 10 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 11, but q != 11
          have : (q : ZMod 9) = 2 := by
            have : q % 252 = 11 := q_mod
            have h_eq : q = 252 * (q / 252) + 11 := (Nat.div_add_mod q 252).symm.trans (by omega)
            have h_cast : ((q : ℕ) : ZMod 9) = (((252 * (q / 252) + 11 : ℕ) : ZMod 9)) := congrArg Nat.cast h_eq
            push_cast at h_cast
            have h252 : (252 : ZMod 9) = 0 := by decide
            rw [h252, zero_mul, zero_add] at h_cast
            exact h_cast
          have h_zmod_9 : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := by
            have h_ge : q ^ f ≥ 3 ^ e := by
              by_contra hc
              have : q ^ f - 3 ^ e = 0 := Nat.sub_eq_zero_of_le (by omega)
              omega
            have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 9) = ((2 : ℕ) : ZMod 9) := congrArg Nat.cast h
            rw [Nat.cast_sub h_ge] at h_cast
            push_cast at h_cast
            exact h_cast
          have h3e_9 : (3 : ZMod 9) ^ e = 0 := by
            have he_eq : e = (e - 3) + 3 := by omega
            rw [he_eq, pow_add]
            have : (3 : ZMod 9) ^ 3 = 0 := rfl
            rw [this, mul_zero]
          rw [this, h3e_9, sub_zero] at h_zmod_9
          have h2f : (2 : ZMod 9) ^ f = (2 : ZMod 9) ^ (f % 6) := by
            have h_eq : f = 6 * (f / 6) + f % 6 := (Nat.div_add_mod f 6).symm
            conv_lhs => rw [h_eq]
            rw [pow_add, pow_mul]
            have : (2 : ZMod 9) ^ 6 = 1 := by decide
            rw [this, one_pow, one_mul]
          rw [h2f] at h_zmod_9
          have hf_mod : f % 6 < 6 := Nat.mod_lt _ (by decide)
          interval_cases hf_mod_val : f % 6 <;> revert h_zmod_9 <;> decide
        · exact non_coprime_contradiction q 252 12 12 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 13
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 13 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (4 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 4 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 14 14 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 3 15 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 4 16 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 17
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 17 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (8 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 8 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 18 18 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 19
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 19 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (1 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 1 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 4 20 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 21 21 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 2 22 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exfalso
          have : q = 23 := by
            have : q % 252 = 23 := q_mod
            omega
          exact hq23 this
        · exact non_coprime_contradiction q 252 12 24 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 25
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 25 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (7 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 7 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 2 26 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 9 27 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 28 28 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 29, but q != 29
          by_cases he_eq : e = 3
          · subst he_eq
            have h_eq : q ^ f = 29 := by omega
            have h_lt : f < 2 := by
              by_contra hc
              have h_ge : f ≥ 2 := by omega
              have : q ^ f ≥ 78961 := by
                calc q ^ f ≥ 281 ^ f := Nat.pow_le_pow_left (by omega) f
                _ ≥ 281 ^ 2 := Nat.pow_le_pow_right (by decide) h_ge
                _ = 78961 := by decide
              omega
            have h_f_pos : f > 0 := by
              by_contra hc
              have : f = 0 := by omega
              subst this
              omega
            have : f = 1 := by omega
            omega
          · have he_gt : e ≥ 4 := lt_cases_exception q e f 3 29 281 hq_ge he3 he_eq (by omega) (by omega) (by decide) (by decide)
            have : (q : ZMod 9) = 2 := by
              have : q % 252 = 29 := q_mod
              have h_eq : q = 252 * (q / 252) + 29 := (Nat.div_add_mod q 252).symm.trans (by omega)
              have h_cast : ((q : ℕ) : ZMod 9) = (((252 * (q / 252) + 29 : ℕ) : ZMod 9)) := congrArg Nat.cast h_eq
              push_cast at h_cast
              have h252 : (252 : ZMod 9) = 0 := by decide
              rw [h252, zero_mul, zero_add] at h_cast
              exact h_cast
            have h_zmod_9 : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := by
              have h_ge : q ^ f ≥ 3 ^ e := by
                by_contra hc
                have : q ^ f - 3 ^ e = 0 := Nat.sub_eq_zero_of_le (by omega)
                omega
              have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 9) = ((2 : ℕ) : ZMod 9) := congrArg Nat.cast h
              rw [Nat.cast_sub h_ge] at h_cast
              push_cast at h_cast
              exact h_cast
            have h3e_9 : (3 : ZMod 9) ^ e = 0 := by
              have he_eq : e = (e - 4) + 4 := by omega
              rw [he_eq, pow_add]
              have : (3 : ZMod 9) ^ 4 = 0 := rfl
              rw [this, mul_zero]
            rw [this, h3e_9, sub_zero] at h_zmod_9
            have h2f : (2 : ZMod 9) ^ f = (2 : ZMod 9) ^ (f % 6) := by
              have h_eq : f = 6 * (f / 6) + f % 6 := (Nat.div_add_mod f 6).symm
              conv_lhs => rw [h_eq]
              rw [pow_add, pow_mul]
              have : (2 : ZMod 9) ^ 6 = 1 := by decide
              rw [this, one_pow, one_mul]
            rw [h2f] at h_zmod_9
            have hf_mod : f % 6 < 6 := Nat.mod_lt _ (by decide)
            interval_cases hf_mod_val : f % 6 <;> revert h_zmod_9 <;> decide
        · exact non_coprime_contradiction q 252 6 30 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 31
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 31 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (4 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 4 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 4 32 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 3 33 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 2 34 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 7 35 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 36 36 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 37
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 37 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (1 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 1 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 2 38 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 3 39 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 4 40 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 41
          have h_zmod_M : (q : ZMod 84) ^ f - (3 : ZMod 84) ^ e = 2 := zmod_equation 3 q e f 84 h
          rw [zmod_cast_of_dvd q 252 84 41 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (41 : ZMod 84) f 36 (by decide)] at h_zmod_M
          rw [pow_three_period e 84 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 84 36 41 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 42 42 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 43
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 43 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (7 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 7 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 4 44 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 9 45 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 2 46 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 47
          have h_zmod_M : (q : ZMod 252) ^ f - (3 : ZMod 252) ^ e = 2 := zmod_equation 3 q e f 252 h
          rw [zmod_cast_of_dvd q 252 252 47 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (47 : ZMod 252) f 72 (by decide)] at h_zmod_M
          rw [pow_three_period e 252 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 252 72 47 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 12 48 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 7 49 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 2 50 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 3 51 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 4 52 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 53
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 53 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (8 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 8 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 18 54 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 55
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 55 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (1 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 1 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 28 56 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 3 57 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 2 58 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 59
          have h_zmod_M : (q : ZMod 252) ^ f - (3 : ZMod 252) ^ e = 2 := zmod_equation 3 q e f 252 h
          rw [zmod_cast_of_dvd q 252 252 59 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (59 : ZMod 252) f 72 (by decide)] at h_zmod_M
          rw [pow_three_period e 252 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 252 72 59 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 12 60 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 61
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 61 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (7 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 7 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 2 62 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 63 63 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 4 64 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 65
          have h_zmod_M : (q : ZMod 63) ^ f - (3 : ZMod 63) ^ e = 2 := zmod_equation 3 q e f 63 h
          rw [zmod_cast_of_dvd q 252 63 65 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (2 : ZMod 63) f 36 (by decide)] at h_zmod_M
          rw [pow_three_period e 63 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 63 36 2 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 6 66 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 67
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 67 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (4 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 4 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 4 68 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 3 69 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 14 70 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 71
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 71 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (8 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 8 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 36 72 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 73
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 73 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (1 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 1 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 2 74 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 3 75 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 4 76 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 7 77 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 6 78 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 79
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 79 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (7 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 7 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 4 80 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 9 81 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 2 82 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 83, but q != 83
          by_cases he_eq : e = 4
          · subst he_eq
            have h_eq : q ^ f = 83 := by omega
            have h_lt : f < 2 := by
              by_contra hc
              have h_ge : f ≥ 2 := by omega
              have : q ^ f ≥ 78961 := by
                calc q ^ f ≥ 281 ^ f := Nat.pow_le_pow_left (by omega) f
                _ ≥ 281 ^ 2 := Nat.pow_le_pow_right (by decide) h_ge
                _ = 78961 := by decide
              omega
            have h_f_pos : f > 0 := by
              by_contra hc
              have : f = 0 := by omega
              subst this
              omega
            have : f = 1 := by omega
            omega
          · have he_gt : e ≥ 5 := lt_cases_exception q e f 4 83 335 hq_ge he3 he_eq (by omega) (by omega) (by decide) (by decide)
            have : (q : ZMod 9) = 2 := by
              have : q % 252 = 83 := q_mod
              have h_eq : q = 252 * (q / 252) + 83 := (Nat.div_add_mod q 252).symm.trans (by omega)
              have h_cast : ((q : ℕ) : ZMod 9) = (((252 * (q / 252) + 83 : ℕ) : ZMod 9)) := congrArg Nat.cast h_eq
              push_cast at h_cast
              have h252 : (252 : ZMod 9) = 0 := by decide
              rw [h252, zero_mul, zero_add] at h_cast
              exact h_cast
            have h_zmod_9 : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := by
              have h_ge : q ^ f ≥ 3 ^ e := by
                by_contra hc
                have : q ^ f - 3 ^ e = 0 := Nat.sub_eq_zero_of_le (by omega)
                omega
              have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 9) = ((2 : ℕ) : ZMod 9) := congrArg Nat.cast h
              rw [Nat.cast_sub h_ge] at h_cast
              push_cast at h_cast
              exact h_cast
            have h3e_9 : (3 : ZMod 9) ^ e = 0 := by
              have he_eq : e = (e - 4) + 4 := by omega
              rw [he_eq, pow_add]
              have : (3 : ZMod 9) ^ 4 = 0 := rfl
              rw [this, mul_zero]
            rw [this, h3e_9, sub_zero] at h_zmod_9
            have h2f : (2 : ZMod 9) ^ f = (2 : ZMod 9) ^ (f % 6) := by
              have h_eq : f = 6 * (f / 6) + f % 6 := (Nat.div_add_mod f 6).symm
              conv_lhs => rw [h_eq]
              rw [pow_add, pow_mul]
              have : (2 : ZMod 9) ^ 6 = 1 := by decide
              rw [this, one_pow, one_mul]
            rw [h2f] at h_zmod_9
            have hf_mod : f % 6 < 6 := Nat.mod_lt _ (by decide)
            interval_cases hf_mod_val : f % 6 <;> revert h_zmod_9 <;> decide
        · exact non_coprime_contradiction q 252 84 84 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 85
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 85 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (4 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 4 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 2 86 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 3 87 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 4 88 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 89
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 89 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (8 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 8 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 18 90 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 7 91 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 4 92 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 3 93 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 2 94 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 95
          have h_zmod_M : (q : ZMod 63) ^ f - (3 : ZMod 63) ^ e = 2 := zmod_equation 3 q e f 63 h
          rw [zmod_cast_of_dvd q 252 63 95 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (32 : ZMod 63) f 36 (by decide)] at h_zmod_M
          rw [pow_three_period e 63 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 63 36 32 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 12 96 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 97
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 97 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (7 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 7 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 14 98 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 9 99 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 4 100 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 101
          have h_zmod_M : (q : ZMod 252) ^ f - (3 : ZMod 252) ^ e = 2 := zmod_equation 3 q e f 252 h
          rw [zmod_cast_of_dvd q 252 252 101 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (101 : ZMod 252) f 72 (by decide)] at h_zmod_M
          rw [pow_three_period e 252 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 252 72 101 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 6 102 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 103
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 103 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (4 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 4 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 4 104 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 21 105 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 2 106 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 107
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 107 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (8 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 8 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 36 108 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 109
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 109 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (1 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 1 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 2 110 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 3 111 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 28 112 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exfalso
          have : q = 113 := by
            have : q % 252 = 113 := q_mod
            omega
          exact hq113 this
        · exact non_coprime_contradiction q 252 6 114 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 115
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 115 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (7 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 7 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 4 116 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 9 117 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 2 118 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 7 119 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 12 120 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 121
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 121 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (4 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 4 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 2 122 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 3 123 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 4 124 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 125
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 125 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (8 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 8 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 126 126 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 127
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 127 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (1 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 1 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 4 128 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 3 129 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 2 130 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exfalso
          have : q = 131 := by
            have : q % 252 = 131 := q_mod
            omega
          exact hq131 this
        · exact non_coprime_contradiction q 252 12 132 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 7 133 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 2 134 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 9 135 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 4 136 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 137
          have h_zmod_M : (q : ZMod 252) ^ f - (3 : ZMod 252) ^ e = 2 := zmod_equation 3 q e f 252 h
          rw [zmod_cast_of_dvd q 252 252 137 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (137 : ZMod 252) f 72 (by decide)] at h_zmod_M
          rw [pow_three_period e 252 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 252 72 137 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 6 138 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 139
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 139 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (4 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 4 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 28 140 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 3 141 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 2 142 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 143
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 143 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (8 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 8 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 36 144 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 145
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 145 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (1 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 1 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 2 146 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 21 147 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 4 148 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 149
          have h_zmod_M : (q : ZMod 252) ^ f - (3 : ZMod 252) ^ e = 2 := zmod_equation 3 q e f 252 h
          rw [zmod_cast_of_dvd q 252 252 149 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (149 : ZMod 252) f 72 (by decide)] at h_zmod_M
          rw [pow_three_period e 252 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 252 72 149 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 6 150 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 151
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 151 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (7 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 7 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 4 152 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 9 153 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 14 154 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 155
          have h_zmod_M : (q : ZMod 84) ^ f - (3 : ZMod 84) ^ e = 2 := zmod_equation 3 q e f 84 h
          rw [zmod_cast_of_dvd q 252 84 155 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (71 : ZMod 84) f 36 (by decide)] at h_zmod_M
          rw [pow_three_period e 84 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 84 36 71 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 12 156 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 157
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 157 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (4 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 4 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 2 158 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 3 159 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 4 160 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 7 161 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 18 162 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 163
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 163 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (1 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 1 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 4 164 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 3 165 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 2 166 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exfalso
          have : q = 167 := by
            have : q % 252 = 167 := q_mod
            omega
          exact hq167 this
        · exact non_coprime_contradiction q 252 84 168 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 169
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 169 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (7 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 7 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 2 170 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 9 171 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 4 172 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exfalso
          have : q = 173 := by
            have : q % 252 = 173 := q_mod
            omega
          exact hq173 this
        · exact non_coprime_contradiction q 252 6 174 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 7 175 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 4 176 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 3 177 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 2 178 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 179
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 179 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (8 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 8 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 36 180 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 181
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 181 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (1 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 1 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 14 182 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 3 183 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 4 184 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exfalso
          have : q = 185 := by
            have : q % 252 = 185 := q_mod
            omega
          have hq_prime : Nat.Prime 185 := by
            rw [← this]
            exact hq
          revert hq_prime
          decide
        · exact non_coprime_contradiction q 252 6 186 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 187
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 187 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (7 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 7 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 4 188 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 63 189 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 2 190 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 191
          have h_zmod_M : (q : ZMod 63) ^ f - (3 : ZMod 63) ^ e = 2 := zmod_equation 3 q e f 63 h
          rw [zmod_cast_of_dvd q 252 63 191 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (2 : ZMod 63) f 36 (by decide)] at h_zmod_M
          rw [pow_three_period e 63 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 63 36 2 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 12 192 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 193
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 193 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (4 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 4 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 2 194 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 3 195 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 28 196 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 197
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 197 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (8 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 8 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 18 198 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 199
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 199 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (1 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 1 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 4 200 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 3 201 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 2 202 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 7 203 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 12 204 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 205
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 205 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (7 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 7 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 2 206 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 9 207 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 4 208 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 209
          have h_zmod_M : (q : ZMod 84) ^ f - (3 : ZMod 84) ^ e = 2 := zmod_equation 3 q e f 84 h
          rw [zmod_cast_of_dvd q 252 84 209 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (41 : ZMod 84) f 36 (by decide)] at h_zmod_M
          rw [pow_three_period e 84 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 84 36 41 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 42 210 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 211
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 211 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (4 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 4 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 4 212 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 3 213 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 2 214 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 215
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 215 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (8 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 8 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 36 216 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 7 217 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 2 218 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 3 219 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 4 220 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 221
          have h_zmod_M : (q : ZMod 63) ^ f - (3 : ZMod 63) ^ e = 2 := zmod_equation 3 q e f 63 h
          rw [zmod_cast_of_dvd q 252 63 221 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (32 : ZMod 63) f 36 (by decide)] at h_zmod_M
          rw [pow_three_period e 63 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 63 36 32 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 6 222 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 223
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 223 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (7 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 7 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 28 224 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 9 225 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 2 226 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 227, but q != 227
          by_cases he_eq : e = 5
          · subst he_eq
            have h_eq : q ^ f = 245 := by omega
            have h_lt : f < 2 := by
              by_contra hc
              have h_ge : f ≥ 2 := by omega
              have : q ^ f ≥ 78961 := by
                calc q ^ f ≥ 281 ^ f := Nat.pow_le_pow_left (by omega) f
                _ ≥ 281 ^ 2 := Nat.pow_le_pow_right (by decide) h_ge
                _ = 78961 := by decide
              omega
            have h_f_pos : f > 0 := by
              by_contra hc
              have : f = 0 := by omega
              subst this
              omega
            have : f = 1 := by omega
            omega
          · have he_gt : e ≥ 6 := lt_cases_exception q e f 5 245 479 hq_ge he3 he_eq (by omega) (by omega) (by decide) (by decide)
            have : (q : ZMod 9) = 2 := by
              have : q % 252 = 227 := q_mod
              have h_eq : q = 252 * (q / 252) + 227 := (Nat.div_add_mod q 252).symm.trans (by omega)
              have h_cast : ((q : ℕ) : ZMod 9) = (((252 * (q / 252) + 227 : ℕ) : ZMod 9)) := congrArg Nat.cast h_eq
              push_cast at h_cast
              have h252 : (252 : ZMod 9) = 0 := by decide
              rw [h252, zero_mul, zero_add] at h_cast
              exact h_cast
            have h_zmod_9 : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := by
              have h_ge : q ^ f ≥ 3 ^ e := by
                by_contra hc
                have : q ^ f - 3 ^ e = 0 := Nat.sub_eq_zero_of_le (by omega)
                omega
              have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 9) = ((2 : ℕ) : ZMod 9) := congrArg Nat.cast h
              rw [Nat.cast_sub h_ge] at h_cast
              push_cast at h_cast
              exact h_cast
            have h3e_9 : (3 : ZMod 9) ^ e = 0 := by
              have he_eq : e = (e - 4) + 4 := by omega
              rw [he_eq, pow_add]
              have : (3 : ZMod 9) ^ 4 = 0 := rfl
              rw [this, mul_zero]
            rw [this, h3e_9, sub_zero] at h_zmod_9
            have h2f : (2 : ZMod 9) ^ f = (2 : ZMod 9) ^ (f % 6) := by
              have h_eq : f = 6 * (f / 6) + f % 6 := (Nat.div_add_mod f 6).symm
              conv_lhs => rw [h_eq]
              rw [pow_add, pow_mul]
              have : (2 : ZMod 9) ^ 6 = 1 := by decide
              rw [this, one_pow, one_mul]
            rw [h2f] at h_zmod_9
            have hf_mod : f % 6 < 6 := Nat.mod_lt _ (by decide)
            interval_cases hf_mod_val : f % 6 <;> revert h_zmod_9 <;> decide
        · exact non_coprime_contradiction q 252 12 228 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 229
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 229 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (4 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 4 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 2 230 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 21 231 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 4 232 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 233
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 233 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (8 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 8 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 18 234 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 235
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 235 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (1 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 1 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 4 236 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 3 237 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 14 238 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 239
          have h_zmod_M : (q : ZMod 84) ^ f - (3 : ZMod 84) ^ e = 2 := zmod_equation 3 q e f 84 h
          rw [zmod_cast_of_dvd q 252 84 239 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (71 : ZMod 84) f 36 (by decide)] at h_zmod_M
          rw [pow_three_period e 84 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 84 36 71 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 12 240 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 241
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 241 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (7 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 7 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 2 242 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 9 243 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 4 244 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 7 245 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 6 246 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 247
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 247 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (4 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 4 f e (by decide) h_zmod_M (by decide)
        · exact non_coprime_contradiction q 252 4 248 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 3 249 hq_coprime (by decide) (by decide) q_mod (by decide)
        · exact non_coprime_contradiction q 252 2 250 hq_coprime (by decide) (by decide) q_mod (by decide)
        · -- q % 252 = 251
          have h_zmod_M : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := zmod_equation 3 q e f 9 h
          rw [zmod_cast_of_dvd q 252 9 251 (by decide) q_mod] at h_zmod_M
          rw [pow_mod_period (8 : ZMod 9) f 6 (by decide)] at h_zmod_M
          rw [pow_three_period e 9 (by omega) (by decide)] at h_zmod_M
          exact no_sol_contradiction 9 6 8 f e (by decide) h_zmod_M (by decide)
            rw [hq_pow_even, h3e_even] at h_zmod
            revert h_zmod; decide
    · subst hp5
      have he3 : e ≥ 3 := by
        by_contra hc
        have : e = 2 := by omega
        subst this
        have : 5 ^ 2 < 27 := by decide
        omega
      rcases hq_cases with hq2 | hq3 | hq5 | hq7 | hq_ge11
      · contradiction
      · subst hq3
        have he_eq2 : e = 2 := (pillai_diff_two_5_3 e f he hf h).1
        omega
      · exact (q_ne_p_of_diff_two 5 q e f hp he h hq5).elim
      · subst hq7
        exact pillai_diff_two_5_7 e f he h
      · exfalso
        -- q >= 11
        have h_zmod : (q : ZMod 3) ^ f - (5 : ZMod 3) ^ e = 2 := by
          have h_ge : q ^ f ≥ 5 ^ e := by omega
          have h_cast : ((q ^ f - 5 ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h
          rw [Nat.cast_sub h_ge] at h_cast
          push_cast at h_cast
          exact h_cast
        -- f % 2 = 0 (even) contradiction from f_even_contradiction
        have hf_even : f % 2 = 0 ∨ f % 2 = 1 := Nat.mod_two_eq_zero_or_one f
        rcases hf_even with hf_even | hf_odd
        · have h_sq : q ^ f = 5 ^ e + 2 := by omega
          exact f_even_contradiction e f q hq hq_ne_2 h_sq hf_even (by omega)
        · -- f is odd, so q^f = q mod 8 and 5^e = 5 mod 8 => q = 7 mod 8
          -- Modulo 3: q % 3 can only be 1 or 2 (since q >= 11)
          have hq3 : q % 3 < 3 := Nat.mod_lt q (by decide)
          interval_cases hq3_val : q % 3
          · have : 3 ∣ q := Nat.dvd_of_mod_eq_zero hq3_val
            rcases hq.eq_one_or_self_of_dvd 3 this with h1 | h2
            · contradiction
            · subst h2; omega
          · -- q % 3 = 1 => q^f % 3 = 1 => 1 - 5^e = 2 => 5^e = 2 mod 3 => e is odd
            have he_odd : e % 2 = 1 := by
              by_contra hc
              have he_even : e % 2 = 0 := by omega
              have h5e : (5 : ZMod 3) ^ e = 1 := by
                have h_eq : e = 2 * (e / 2) := by omega
                rw [h_eq, pow_mul]
                have : (5 : ZMod 3) ^ 2 = 1 := rfl
                rw [this, one_pow]
              have hq1 : (q : ZMod 3) = 1 := by
                have : q % 3 = 1 := hq3_val
                have h_cast : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
                rw [h_cast, this]
                rfl
              have h_zmod_local : (q : ZMod 3) ^ f - (5 : ZMod 3) ^ e = 2 := h_zmod
              rw [hq1, one_pow, h5e] at h_zmod_local
              revert h_zmod_local; decide
            -- Since e is odd => 5^e = 5 mod 8. Since f is odd => q^f = q mod 8.
            -- So q - 5 = 2 mod 8 => q = 7 mod 8.
            -- Since q % 3 = 1 and q % 8 = 7 => q % 24 = 7.
            -- Modulo 5: Since e >= 3 => 5^e = 0 mod 125 => q^f = 2 mod 25 => q = 2 or 3 mod 5
            -- If q = 2 mod 5, then q = 7 mod 25 (since q % 24 = 7 is not used here, but q % 252 is. 
            -- Actually we can just do interval_cases q % 5)
            have hq5 : q % 5 < 5 := Nat.mod_lt q (by decide)
            interval_cases hq5_val : q % 5
            · have : 5 ∣ q := Nat.dvd_of_mod_eq_zero hq5_val
              rcases hq.eq_one_or_self_of_dvd 5 this with h1 | h2
              · contradiction
              · subst h2; omega
            · -- q % 5 = 1 => q^f = 1 mod 5 => 1 - 0 = 2 => 1 = 2 mod 5 (since e >= 3 => 5^e = 0 mod 5)
              have h_zmod5 : (q : ZMod 5) ^ f - (5 : ZMod 5) ^ e = 2 := by
                have h_ge : q ^ f ≥ 5 ^ e := by omega
                have h_cast : ((q ^ f - 5 ^ e : ℕ) : ZMod 5) = ((2 : ℕ) : ZMod 5) := congrArg Nat.cast h
                rw [Nat.cast_sub h_ge] at h_cast
                push_cast at h_cast
                exact h_cast
              have hq1 : (q : ZMod 5) = 1 := by
                have : q % 5 = 1 := hq5_val
                have h_cast : ((q : ℕ) : ZMod 5) = ((q % 5 : ℕ) : ZMod 5) := by rw [ZMod.natCast_mod]
                rw [h_cast, this]
                rfl
              have h5e : (5 : ZMod 5) ^ e = 0 := by
                have he_eq : e = (e - 1) + 1 := by omega
                rw [he_eq, pow_succ]
                have : (5 : ZMod 5) = 0 := rfl
                rw [this, mul_zero]
              rw [hq1, one_pow, h5e, sub_zero] at h_zmod5
              revert h_zmod5; decide
            · -- q % 5 = 2 => q^f = 2^f mod 5 => 2^f - 0 = 2 => 2^f = 2 mod 5 => f % 4 = 1
              -- q % 25 = 7 (since q % 5 = 2). Powers of 7 mod 25: 7, 24, 18, 1 => never 2!
              -- So q^f = 2 mod 25 is impossible!
              -- We can prove this by interval_cases q % 25
              have h_zmod25 : (q : ZMod 25) ^ f - (5 : ZMod 25) ^ e = 2 := by
                have h_ge : q ^ f ≥ 5 ^ e := by omega
                have h_cast : ((q ^ f - 5 ^ e : ℕ) : ZMod 25) = ((2 : ℕ) : ZMod 25) := congrArg Nat.cast h
                rw [Nat.cast_sub h_ge] at h_cast
                push_cast at h_cast
                exact h_cast
              have h5e25 : (5 : ZMod 25) ^ e = 0 := by
                have he_eq : e = (e - 2) + 2 := by omega
                rw [he_eq, pow_add]
                have : (5 : ZMod 25) ^ 2 = 0 := rfl
                rw [this, mul_zero]
              rw [h5e25, sub_zero] at h_zmod25
              have hq25 : q % 25 < 25 := Nat.mod_lt q (by decide)
              have h_eq_mod : q % 5 = 2 := hq5_val
              -- This forces q % 25 in [2, 7, 12, 17, 22]
              interval_cases hq25_val : q % 25
              · exact False.elim (dvd_contradiction_25 q hq hq5_val (Nat.dvd_of_mod_eq_zero hq25_val))
              · exfalso; have : q % 5 = 1 := by omega; omega
              · -- q % 25 = 2 => (q : ZMod 25) = 2.
                have h_zmod8 : (q : ZMod 8) ^ f - (5 : ZMod 8) ^ e = 2 := by
                  have h_ge : q ^ f ≥ 5 ^ e := by omega
                  have h_cast : ((q ^ f - 5 ^ e : ℕ) : ZMod 8) = ((2 : ℕ) : ZMod 8) := congrArg Nat.cast h
                  rw [Nat.cast_sub h_ge] at h_cast
                  push_cast at h_cast
                  exact h_cast
                have h_cast_q : (q : ZMod 8) = 7 := by
                  have hq8 : q % 8 = 7 := by
                    have hq8_lt : q % 8 < 8 := Nat.mod_lt q (by decide)
                    interval_cases hq8_val : q % 8
                    · exact False.elim (dvd_contradiction_eight q hq hq_ne_2 (Nat.dvd_of_mod_eq_zero hq8_val))
                    · exfalso
                      have hq1 : (q : ZMod 3) = 1 := by
                        have : q % 3 = 1 := hq3_val
                        have h_cast : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
                        rw [h_cast, this]
                        rfl
                      have h_zmod_local : (q : ZMod 3) ^ f - (5 : ZMod 3) ^ e = 2 := h_zmod
                      have h5e : (5 : ZMod 3) ^ e = 2 := by
                        have : (5 : ZMod 3) = 2 := rfl
                        rw [this]
                        have h_eq : e = 2 * (e / 2) + 1 := by omega
                        rw [h_eq]
                        have : (2 : ZMod 3) ^ (2 * (e / 2) + 1) = ((2 : ZMod 3) ^ 2) ^ (e / 2) * 2 := by
                          rw [pow_succ, pow_mul]
                        rw [this]
                        have : (2 : ZMod 3) ^ 2 = 1 := rfl
                        rw [this, one_pow, one_mul]
                      rw [hq1, one_pow, h5e] at h_zmod_local
                      revert h_zmod_local; decide
                    · exfalso; have : q % 2 = 0 := by omega; omega
                    · exfalso; have : q % 8 = 3 := hq8_val; omega
                    · exfalso; have : q % 2 = 0 := by omega; omega
                    · exfalso; have : q % 8 = 5 := hq8_val; omega
                    · exfalso; have : q % 2 = 0 := by omega; omega
                    · exact hq8_val
                  have h_cast : ((q : ℕ) : ZMod 8) = ((q % 8 : ℕ) : ZMod 8) := by rw [ZMod.natCast_mod]
                  rw [h_cast, hq8]
                  rfl
                -- Let us clear some variables to avoid timeouts
                clear h hlt hq_ne_2 hq_ge11 hq3 hq3_val hq5_val he_odd h_zmod5 hq25 h_zmod25 hq25_val h_zmod
                omega
              · exfalso; have : q % 5 = 3 := by omega; omega
              · exfalso; have : q % 5 = 4 := by omega; omega
              · exfalso; have : q % 5 = 0 := by omega; omega
              · exfalso; have : q % 5 = 1 := by omega; omega
              · -- q % 25 = 7 => (q : ZMod 25) = 7
                have h_cast_q : (q : ZMod 25) = 7 := by
                  have : q % 25 = 7 := hq25_val
                  have h_cast : ((q : ℕ) : ZMod 25) = ((q % 25 : ℕ) : ZMod 25) := by rw [ZMod.natCast_mod]
                  rw [h_cast, this]
                  rfl
                rw [h_cast_q] at h_zmod25
                have h_pow : (7 : ZMod 25) ^ f = (7 : ZMod 25) ^ (f % 4) := by
                  have h_eq : f = 4 * (f / 4) + f % 4 := (Nat.div_add_mod f 4).symm
                  conv_lhs => rw [h_eq]
                  rw [pow_add, pow_mul]
                  have : (7 : ZMod 25) ^ 4 = 1 := by decide
                  rw [this, one_pow, one_mul]
                rw [h_pow] at h_zmod25
                have h_mod : f % 4 < 4 := Nat.mod_lt f (by decide)
                interval_cases h_cases : f % 4 <;> revert h_zmod25 <;> decide
              · exfalso; have : q % 5 = 3 := by omega; omega
              · exfalso; have : q % 5 = 4 := by omega; omega
              · exfalso; have : q % 5 = 0 := by omega; omega
              · exfalso; have : q % 5 = 1 := by omega; omega
              · -- q % 25 = 12
                have : q % 5 = 2 := by
                  have : q % 25 = 12 := hq25_val
                  omega
                omega
              · exfalso; have : q % 5 = 3 := by omega; omega
              · exfalso; have : q % 5 = 4 := by omega; omega
              · exfalso; have : q % 5 = 0 := by omega; omega
              · exfalso; have : q % 5 = 1 := by omega; omega
              · -- q % 25 = 17
                have : q % 5 = 2 := by
                  have : q % 25 = 17 := hq25_val
                  omega
                omega
              · exfalso; have : q % 5 = 3 := by omega; omega
              · exfalso; have : q % 5 = 4 := by omega; omega
              · exfalso; have : q % 5 = 0 := by omega; omega
              · exfalso; have : q % 5 = 1 := by omega; omega
              · -- q % 25 = 22
                have : q % 5 = 2 := by
                  have : q % 25 = 22 := hq25_val
                  omega
                omega
              · exfalso; have : q % 5 = 3 := by omega; omega
              · exfalso; have : q % 5 = 4 := by omega; omega
            · -- q % 5 = 3
              have : q % 5 = 2 := by omega
              omega
            · -- q % 5 = 4
              have : q % 5 = 2 := by omega
              omega
          · -- q % 3 = 2 => q^f % 3 = 2^f % 3 => 2^f - 5^e = 2 => 2^f - 2^e = 2 mod 3 => 2^f - 2^e = 2 mod 3 (since e is odd)
            -- if f is odd => 2 - 2 = 2 => 0 = 2 mod 3 (contradiction).
            -- So f is even => contradiction from f_even_contradiction!
            have h_zmod_local : (q : ZMod 3) ^ f - (5 : ZMod 3) ^ e = 2 := h_zmod
            have hq2 : (q : ZMod 3) = 2 := by
              have : q % 3 = 2 := hq3_val
              have h_cast : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
              rw [h_cast, this]
              rfl
            have h5_2 : (5 : ZMod 3) = 2 := rfl
            have hqf : (2 : ZMod 3) ^ f = 2 := pow_two_zmod_three_odd f hf_odd
            have h5e : (2 : ZMod 3) ^ e = 2 := pow_two_zmod_three_odd e he_odd
            rw [hq2, h5_2] at h_zmod_local
            rw [hqf, h5e] at h_zmod_local
            revert h_zmod_local; decide
    · subst hp7
      rcases hq_cases with hq2 | hq3 | hq5 | hq7 | hq_ge11
      · contradiction
      · subst hq3
        exact pillai_diff_two_7_3 e f he hf h
      · subst hq5
        exact pillai_diff_two_7_5 e f h
      · exact (q_ne_p_of_diff_two 7 q e f hp he h hq7).elim
      · exfalso
        -- q >= 11
        -- Modulo 3: if q = 2 mod 3 => q^f - 7^e = 2 => 2^f - 1 = 2 => 2^f = 0 mod 3 (impossible)
        have hq3 : q % 3 < 3 := Nat.mod_lt q (by decide)
        interval_cases hq3_val : q % 3
        · have : 3 ∣ q := Nat.dvd_of_mod_eq_zero hq3_val
          rcases hq.eq_one_or_self_of_dvd 3 this with h1 | h2
          · contradiction
          · subst h2; omega
        · -- q % 3 = 1 => 1^f - 7^e = 2 => 1 - 1 = 2 => 0 = 2 mod 3 (contradiction)
          have h_zmod : (q : ZMod 3) ^ f - (7 : ZMod 3) ^ e = 2 := by
            have h_ge : q ^ f ≥ 7 ^ e := by omega
            have h_cast : ((q ^ f - 7 ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h
            rw [Nat.cast_sub h_ge] at h_cast
            push_cast at h_cast
            exact h_cast
          have hq1 : (q : ZMod 3) = 1 := by
            have : q % 3 = 1 := hq3_val
            have h_cast : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
            rw [h_cast, this]
            rfl
          have h7e : (7 : ZMod 3) ^ e = 1 := by
            have : (7 : ZMod 3) = 1 := rfl
            rw [this, one_pow]
          rw [hq1, one_pow, h7e] at h_zmod
          revert h_zmod; decide
        · -- q % 3 = 2 => 2^f - 1 = 2 => 2^f = 0 mod 3 (impossible)
          have h_zmod : (q : ZMod 3) ^ f - (7 : ZMod 3) ^ e = 2 := by
            have h_ge : q ^ f ≥ 7 ^ e := by omega
            have h_cast : ((q ^ f - 7 ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h
            rw [Nat.cast_sub h_ge] at h_cast
            push_cast at h_cast
            exact h_cast
          have hq2 : (q : ZMod 3) = 2 := by
            have : q % 3 = 2 := hq3_val
            have h_cast : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
            rw [h_cast, this]
            rfl
          have h7e : (7 : ZMod 3) ^ e = 1 := by
            have : (7 : ZMod 3) = 1 := rfl
            rw [this, one_pow]
          rw [hq2, h7e] at h_zmod
          have h2f : (2 : ZMod 3) ^ f = (2 : ZMod 3) ^ (f % 2) := by
            have h_eq : f = 2 * (f / 2) + f % 2 := (Nat.div_add_mod f 2).symm
            conv_lhs => rw [h_eq]
            rw [pow_add, pow_mul]
            have : (2 : ZMod 3) ^ 2 = 1 := rfl
            rw [this, one_pow, one_mul]
          rw [h2f] at h_zmod
          have h_mod : f % 2 < 2 := Nat.mod_lt f (by decide)
          interval_cases h_cases : f % 2 <;> revert h_zmod <;> decide
    · -- p >= 11
      exfalso
      rcases hq_cases with hq2 | hq3 | hq5 | hq7 | hq_ge11
      · contradiction
      · subst hq3
        have he_eq2 : e = 2 := (pillai_diff_two_5_3 e f he hf h).1
        omega
      · subst hq5
        -- q = 5 => 5^f - p^e = 2 => mod 3 => (-1)^f - p^e = 2
        have hq5_mod3 : (5 : ZMod 3) ^ f - (p : ZMod 3) ^ e = 2 := by
          have h_ge : 5 ^ f ≥ p ^ e := by omega
          have h_cast : ((5 ^ f - p ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h
          rw [Nat.cast_sub h_ge] at h_cast
          push_cast at h_cast
          exact h_cast
        have h5 : (5 : ZMod 3) = 2 := rfl
        rw [h5] at hq5_mod3
        -- since p >= 11 => p % 3 can be 1 or 2
        have hp3 : p % 3 < 3 := Nat.mod_lt p (by decide)
        interval_cases hp3_val : p % 3
        · have : 3 ∣ p := Nat.dvd_of_mod_eq_zero hp3_val
          rcases hp.eq_one_or_self_of_dvd 3 this with h1 | h2
          · contradiction
          · subst h2; omega
        · -- p % 3 = 1 => 2^f - 1 = 2 => 2^f = 0 mod 3 (impossible)
          have hp1 : (p : ZMod 3) = 1 := by
            have : p % 3 = 1 := hp3_val
            have h_cast : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
            rw [h_cast, this]
            rfl
          rw [hp1, one_pow] at hq5_mod3
          have h2f : (2 : ZMod 3) ^ f = (2 : ZMod 3) ^ (f % 2) := by
            have h_eq : f = 2 * (f / 2) + f % 2 := (Nat.div_add_mod f 2).symm
            conv_lhs => rw [h_eq]
            rw [pow_add, pow_mul]
            have : (2 : ZMod 3) ^ 2 = 1 := rfl
            rw [this, one_pow, one_mul]
          rw [h2f] at hq5_mod3
          have h_mod : f % 2 < 2 := Nat.mod_lt f (by decide)
          interval_cases h_cases : f % 2 <;> revert hq5_mod3 <;> decide
        · -- p % 3 = 2 => 2^f - 2^e = 2 => if e is even => 2^f - 1 = 2 (impossible). If e is odd => 2^f - 2 = 2 => 2^f = 1 (forces f even)
          have he_even : e % 2 = 0 ∨ e % 2 = 1 := Nat.mod_two_eq_zero_or_one e
          rcases he_even with he_even | he_odd
          · have hp2 : (p : ZMod 3) = 2 := by
              have : p % 3 = 2 := hp3_val
              have h_cast : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
              rw [h_cast, this]
              rfl
            have hp_pow : (2 : ZMod 3) ^ e = 1 := by
              have h_eq : e = 2 * (e / 2) := by omega
              rw [h_eq, pow_mul]
              have : (2 : ZMod 3) ^ 2 = 1 := rfl
              rw [this, one_pow]
            rw [hp2, hp_pow] at hq5_mod3
            have h2f : (2 : ZMod 3) ^ f = (2 : ZMod 3) ^ (f % 2) := by
              have h_eq : f = 2 * (f / 2) + f % 2 := (Nat.div_add_mod f 2).symm
              conv_lhs => rw [h_eq]
              rw [pow_add, pow_mul]
              have : (2 : ZMod 3) ^ 2 = 1 := rfl
              rw [this, one_pow, one_mul]
            rw [h2f] at hq5_mod3
            have h_mod : f % 2 < 2 := Nat.mod_lt f (by decide)
            interval_cases h_cases : f % 2 <;> revert hq5_mod3 <;> decide
          · have hf_even : f % 2 = 0 ∨ f % 2 = 1 := Nat.mod_two_eq_zero_or_one f
            rcases hf_even with hf_even | hf_odd
            · have h_sq : 5 ^ f = 5 ^ e + 2 := by omega
              exact f_even_contradiction e f 5 Nat.prime_five (by decide) h_sq hf_even (by omega)
            · -- e is odd, f is odd => 2^f - 2^e = 2 => 2 - 2 = 2 => 0 = 2 mod 3 (contradiction)
              have hp2 : (p : ZMod 3) = 2 := by
                have : p % 3 = 2 := hp3_val
                have h_cast : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
                rw [h_cast, this]
                rfl
              have hp_pow : (2 : ZMod 3) ^ e = 2 := by
                have h_eq : e = 2 * (e / 2) + 1 := by omega
                rw [h_eq]
                have : (2 : ZMod 3) ^ (2 * (e / 2) + 1) = ((2 : ZMod 3) ^ 2) ^ (e / 2) * 2 := by
                  rw [pow_succ, pow_mul]
                rw [this]
                have : (2 : ZMod 3) ^ 2 = 1 := rfl
                rw [this, one_pow, one_mul]
              have hq_pow : (2 : ZMod 3) ^ f = 2 := by
                have h_eq : f = 2 * (f / 2) + 1 := by omega
                rw [h_eq]
                have : (2 : ZMod 3) ^ (2 * (f / 2) + 1) = ((2 : ZMod 3) ^ 2) ^ (e / 2) * 2 := by
                  rw [pow_succ, pow_mul]
                rw [this]
                have : (2 : ZMod 3) ^ 2 = 1 := rfl
                rw [this, one_pow, one_mul]
              rw [hp2, hp_pow, hq_pow] at hq5_mod3
              revert hq5_mod3; decide
      · subst hq7
        -- q = 7 => 7^f - p^e = 2 => mod 3 => 1^f - p^e = 2 => 1 - p^e = 2 => p^e = 2 mod 3 => p = 2 mod 3 and e is odd
        -- then mod 8 => since f is odd (if f is even, q^f = 1 mod 8 => 1 - p^e = 2 => p^e = 7 => p = 7 mod 8)
        -- wait, if f is even, we can use q = 7 => 7^f - p^e = 2.
        -- actually let us check if f is even: f % 2 = 0 => (7^j)^2 - p^e = 2 => 1 - p^e = 2 => p^e = 7 => p = 7 mod 8.
        -- and p = 2 mod 3 => p = 23 mod 24.
        -- wait, we can just do a general mod 3 and mod 8 contradiction
        have h_zmod3 : (7 : ZMod 3) ^ f - (p : ZMod 3) ^ e = 2 := by
          have h_ge : 7 ^ f ≥ p ^ e := by omega
          have h_cast : ((7 ^ f - p ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h
          rw [Nat.cast_sub h_ge] at h_cast
          push_cast at h_cast
          exact h_cast
        have h7 : (7 : ZMod 3) = 1 := rfl
        rw [h7, one_pow] at h_zmod3
        -- since p >= 11 => p % 3 can be 1 or 2
        have hp3 : p % 3 < 3 := Nat.mod_lt p (by decide)
        interval_cases hp3_val : p % 3
        · have : 3 ∣ p := Nat.dvd_of_mod_eq_zero hp3_val
          rcases hp.eq_one_or_self_of_dvd 3 this with h1 | h2
          · contradiction
          · subst h2; omega
        · -- p % 3 = 1 => 1 - 1^e = 2 => 0 = 2 mod 3
          have hp1 : (p : ZMod 3) = 1 := by
            have : p % 3 = 1 := hp3_val
            have h_cast : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
            rw [h_cast, this]
            rfl
          rw [hp1, one_pow] at h_zmod3
          revert h_zmod3; decide
        · -- p % 3 = 2 => 1 - 2^e = 2 => 2^e = 2 mod 3 => e is odd
          have he_even : e % 2 = 0 ∨ e % 2 = 1 := Nat.mod_two_eq_zero_or_one e
          rcases he_even with he_even | he_odd
          · have hp2 : (p : ZMod 3) = 2 := by
              have : p % 3 = 2 := hp3_val
              have h_cast : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
              rw [h_cast, this]
              rfl
            have hp_pow : (2 : ZMod 3) ^ e = 1 := by
              have h_eq : e = 2 * (e / 2) := by omega
              rw [h_eq, pow_mul]
              have : (2 : ZMod 3) ^ 2 = 1 := rfl
              rw [this, one_pow]
            rw [hp2, hp_pow] at h_zmod3
            revert h_zmod3; decide
          · -- e is odd => p^e = p mod 8. Since q = 7 => 7^f - p^e = 2 => if f is even, 1 - p = 2 => p = 7 mod 8
            -- if f is odd => 7 - p = 2 => p = 5 mod 8
            -- let us check if f is even or odd
            have hf_even : f % 2 = 0 ∨ f % 2 = 1 := Nat.mod_two_eq_zero_or_one f
            rcases hf_even with hf_even | hf_odd
            · -- f is even => 1 - p = 2 mod 8 => p = 7 mod 8
              have h_zmod8 : (7 : ZMod 8) ^ f - (p : ZMod 8) ^ e = 2 := by
                have h_ge : 7 ^ f ≥ p ^ e := by omega
                have h_cast : ((7 ^ f - p ^ e : ℕ) : ZMod 8) = ((2 : ℕ) : ZMod 8) := congrArg Nat.cast h
                rw [Nat.cast_sub h_ge] at h_cast
                push_cast at h_cast
                exact h_cast
              have h7f : (7 : ZMod 8) ^ f = 1 := by
                have h_eq : f = 2 * (f / 2) := by omega
                rw [h_eq, pow_mul]
                have : (7 : ZMod 8) ^ 2 = 1 := rfl
                rw [this, one_pow]
              have hpe : (p : ZMod 8) ^ e = (p : ZMod 8) := by
                have h_eq : e = 2 * (e / 2) + 1 := by omega
                rw [h_eq]
                have : (p : ZMod 8) ^ (2 * (e / 2) + 1) = ((p : ZMod 8) ^ 2) ^ (e / 2) * (p : ZMod 8) := by
                  rw [pow_succ, pow_mul]
                rw [this]
                have hp_odd : p % 2 = 1 := by
                  by_contra hc_p
                  have : 2 ∣ p := Nat.dvd_of_mod_eq_zero (by omega)
                  rcases hp.eq_one_or_self_of_dvd 2 this with h1 | h2
                  · contradiction
                  · subst h2; omega
                have : (p : ZMod 8) ^ 2 = 1 := by
                  have h_mod : p % 8 < 8 := Nat.mod_lt p (by decide)
                  interval_cases hp_mod : p % 8
                  · exact False.elim (dvd_contradiction_eight p hp hp_ne_2 (Nat.dvd_of_mod_eq_zero hp_mod))
                  · rw [zmod_cast_8 p 1 hp_mod]; rfl
                  · exfalso; have : p % 2 = 0 := by omega; omega
                  · rw [zmod_cast_8 p 3 hp_mod]; rfl
                  · exfalso; have : p % 2 = 0 := by omega; omega
                  · rw [zmod_cast_8 p 5 hp_mod]; rfl
                  · exfalso; have : p % 2 = 0 := by omega; omega
                  · rw [zmod_cast_8 p 7 hp_mod]; rfl
                rw [this, one_pow, one_mul]
              rw [h7f, hpe] at h_zmod8
              -- so 1 - p = 2 mod 8 => p = 7 mod 8 => p = 23 mod 24 (since p = 2 mod 3)
              -- let us use mod 5: since p >= 11 and p = 23 mod 24 => p % 5 can be 1, 2, 3, 4
              -- actually, we can just do interval_cases p % 5
              have hp5 : p % 5 < 5 := Nat.mod_lt p (by decide)
              interval_cases hp5_val : p % 5
              · have : 5 ∣ p := Nat.dvd_of_mod_eq_zero hp5_val
                rcases hp.eq_one_or_self_of_dvd 5 this with h1 | h2
                · contradiction
                · subst h2; omega
              · -- p = 1 mod 5 => 7^f - p^e = 2 => if f is even, let f = 2j => 49^j - p^e = 2 => (-1)^j - 1 = 2 => -1 - 1 = 2 or 1 - 1 = 2 mod 5 (impossible)
                have h_zmod5 : (7 : ZMod 5) ^ f - (p : ZMod 5) ^ e = 2 := by
                  have h_ge : 7 ^ f ≥ p ^ e := by omega
                  have h_cast : ((7 ^ f - p ^ e : ℕ) : ZMod 5) = ((2 : ℕ) : ZMod 5) := congrArg Nat.cast h
                  rw [Nat.cast_sub h_ge] at h_cast
                  push_cast at h_cast
                  exact h_cast
                have hp1 : (p : ZMod 5) = 1 := by
                  have : p % 5 = 1 := hp5_val
                  have h_cast : ((p : ℕ) : ZMod 5) = ((p % 5 : ℕ) : ZMod 5) := by rw [ZMod.natCast_mod]
                  rw [h_cast, this]
                  rfl
                have h7f_even : (7 : ZMod 5) ^ f = (7 : ZMod 5) ^ (f % 4) := by
                  have h_eq : f = 4 * (f / 4) + f % 4 := (Nat.div_add_mod f 4).symm
                  conv_lhs => rw [h_eq]
                  rw [pow_add, pow_mul]
                  have : (7 : ZMod 5) ^ 4 = 1 := by decide
                  rw [this, one_pow, one_mul]
                rw [hp1, one_pow, h7f_even] at h_zmod5
                have h_mod_f : f % 4 < 4 := Nat.mod_lt f (by decide)
                have hf_even2 : f % 4 = 0 ∨ f % 4 = 2 := by
                  have : f % 2 = 0 := hf_even
                  omega
                rcases hf_even2 with hf0 | hf2
                · rw [hf0] at h_zmod5; revert h_zmod5; decide
                · rw [hf2] at h_zmod5; revert h_zmod5; decide
              · -- p = 2 mod 5 => if f is even, 7^f - p^e = 2 mod 5 => if f % 4 = 0 => 1 - 2^e = 2 => 2^e = 4 => e is even (contradiction)
                -- if f % 4 = 2 => 4 - 2^e = 2 => 2^e = 2 => e % 4 = 1
                -- if e % 4 = 1 => mod 13 or mod 11
                omega
              · subst hp3 mod 5
                omega
              · -- p = 4 mod 5
                omega
            · -- f is odd => 7 - p = 2 mod 8 => p = 5 mod 8 => p = 5 mod 24 => mod 5
              omega
      · -- p >= 11, q >= 11
        have hp3 : p % 3 < 3 := Nat.mod_lt p (by decide)
        have hq3 : q % 3 < 3 := Nat.mod_lt q (by decide)
        interval_cases hp3_val : p % 3 <;> interval_cases hq3_val : q % 3
        · have : 3 ∣ p := Nat.dvd_of_mod_eq_zero hp3_val
          rcases hp.eq_one_or_self_of_dvd 3 this with h1 | h2
          · contradiction
          · subst h2; omega
        · have : 3 ∣ p := Nat.dvd_of_mod_eq_zero hp3_val
          rcases hp.eq_one_or_self_of_dvd 3 this with h1 | h2
          · contradiction
          · subst h2; omega
        · have : 3 ∣ p := Nat.dvd_of_mod_eq_zero hp3_val
          rcases hp.eq_one_or_self_of_dvd 3 this with h1 | h2
          · contradiction
          · subst h2; omega
        · have : 3 ∣ q := Nat.dvd_of_mod_eq_zero hq3_val
          rcases hq.eq_one_or_self_of_dvd 3 this with h1 | h2
          · contradiction
          · subst h2; omega
        · -- p = 1, q = 1 => q^f - p^e = 2 mod 3 => 1 - 1 = 2 => 0 = 2 mod 3 (contradiction)
          have h_zmod3 : (q : ZMod 3) ^ f - (p : ZMod 3) ^ e = 2 := by
            have h_ge : q ^ f ≥ p ^ e := by omega
            have h_cast : ((q ^ f - p ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h
            rw [Nat.cast_sub h_ge] at h_cast
            push_cast at h_cast
            exact h_cast
          have hp1 : (p : ZMod 3) = 1 := by
            have : p % 3 = 1 := hp3_val
            have h_cast : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
            rw [h_cast, this]
            rfl
          have hq1 : (q : ZMod 3) = 1 := by
            have : q % 3 = 1 := hq3_val
            have h_cast : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
            rw [h_cast, this]
            rfl
          rw [hp1, hq1, one_pow, one_pow] at h_zmod3
          revert h_zmod3; decide
        · -- p = 1, q = 2 => q^f - p^e = 2 mod 3 => 2^f - 1 = 2 => 2^f = 3 = 0 mod 3 (impossible)
          have h_zmod3 : (q : ZMod 3) ^ f - (p : ZMod 3) ^ e = 2 := by
            have h_ge : q ^ f ≥ p ^ e := by omega
            have h_cast : ((q ^ f - p ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h
            rw [Nat.cast_sub h_ge] at h_cast
            push_cast at h_cast
            exact h_cast
          have hp1 : (p : ZMod 3) = 1 := by
            have : p % 3 = 1 := hp3_val
            have h_cast : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
            rw [h_cast, this]
            rfl
          have hq2 : (q : ZMod 3) = 2 := by
            have : q % 3 = 2 := hq3_val
            have h_cast : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
            rw [h_cast, this]
            rfl
          rw [hp1, hq2, one_pow] at h_zmod3
          have h2f : (2 : ZMod 3) ^ f = (2 : ZMod 3) ^ (f % 2) := by
            have h_eq : f = 2 * (f / 2) + f % 2 := (Nat.div_add_mod f 2).symm
            conv_lhs => rw [h_eq]
            rw [pow_add, pow_mul]
            have : (2 : ZMod 3) ^ 2 = 1 := rfl
            rw [this, one_pow, one_mul]
          rw [h2f] at h_zmod3
          have h_mod : f % 2 < 2 := Nat.mod_lt f (by decide)
          interval_cases h_cases : f % 2 <;> revert h_zmod3 <;> decide
        · have : 3 ∣ q := Nat.dvd_of_mod_eq_zero hq3_val
          rcases hq.eq_one_or_self_of_dvd 3 this with h1 | h2
          · contradiction
          · subst h2; omega
        · -- p = 2, q = 1 => 1^f - 2^e = 2 => 1 - 2^e = 2 => 2^e = 2 mod 3 => e is odd
          have he_even : e % 2 = 0 ∨ e % 2 = 1 := Nat.mod_two_eq_zero_or_one e
          rcases he_even with he_even | he_odd
          · have h_zmod3 : (q : ZMod 3) ^ f - (p : ZMod 3) ^ e = 2 := by
              have h_ge : q ^ f ≥ p ^ e := by omega
              have h_cast : ((q ^ f - p ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h
              rw [Nat.cast_sub h_ge] at h_cast
              push_cast at h_cast
              exact h_cast
            have hp2 : (p : ZMod 3) = 2 := by
              have : p % 3 = 2 := hp3_val
              have h_cast : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
              rw [h_cast, this]
              rfl
            have hq1 : (q : ZMod 3) = 1 := by
              have : q % 3 = 1 := hq3_val
              have h_cast : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
              rw [h_cast, this]
              rfl
            have hp_pow : (2 : ZMod 3) ^ e = 1 := by
              have h_eq : e = 2 * (e / 2) := by omega
              rw [h_eq, pow_mul]
              have : (2 : ZMod 3) ^ 2 = 1 := rfl
              rw [this, one_pow]
            rw [hp2, hq1, one_pow, hp_pow] at h_zmod3
            revert h_zmod3; decide
          · -- e is odd => mod 8 => p^e = p mod 8. If f is even => 1 - p = 2 => p = 7 mod 8 => p = 23 mod 24
            -- if f is odd => q - p = 2 mod 8
            omega
        · -- p = 2, q = 2 => 2^f - 2^e = 2 mod 3 => if e even, 2^f - 1 = 2 (impossible)
          -- if e is odd, 2^f - 2 = 2 => 2^f = 1 (forces f even)
          -- so we must have e is odd and f is even
          have he_even : e % 2 = 0 ∨ e % 2 = 1 := Nat.mod_two_eq_zero_or_one e
          rcases he_even with he_even | he_odd
          · have h_zmod3 : (q : ZMod 3) ^ f - (p : ZMod 3) ^ e = 2 := by
              have h_ge : q ^ f ≥ p ^ e := by omega
              have h_cast : ((q ^ f - p ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h
              rw [Nat.cast_sub h_ge] at h_cast
              push_cast at h_cast
              exact h_cast
            have hp2 : (p : ZMod 3) = 2 := by
              have : p % 3 = 2 := hp3_val
              have h_cast : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
              rw [h_cast, this]
              rfl
            have hq2 : (q : ZMod 3) = 2 := by
              have : q % 3 = 2 := hq3_val
              have h_cast : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
              rw [h_cast, this]
              rfl
            have hp_pow : (2 : ZMod 3) ^ e = 1 := by
              have h_eq : e = 2 * (e / 2) := by omega
              rw [h_eq, pow_mul]
              have : (2 : ZMod 3) ^ 2 = 1 := rfl
              rw [this, one_pow]
            rw [hp2, hq2, hp_pow] at h_zmod3
            have h2f : (2 : ZMod 3) ^ f = (2 : ZMod 3) ^ (f % 2) := by
              have h_eq : f = 2 * (f / 2) + f % 2 := (Nat.div_add_mod f 2).symm
              conv_lhs => rw [h_eq]
              rw [pow_add, pow_mul]
              have : (2 : ZMod 3) ^ 2 = 1 := rfl
              rw [this, one_pow, one_mul]
            rw [h2f] at h_zmod3
            have h_mod : f % 2 < 2 := Nat.mod_lt f (by decide)
            interval_cases h_cases : f % 2 <;> revert h_zmod3 <;> decide
          · have hf_even : f % 2 = 0 ∨ f % 2 = 1 := Nat.mod_two_eq_zero_or_one f
            rcases hf_even with hf_even | hf_odd
            · -- f is even => 1 - p = 2 mod 8 => p = 7 mod 8 => p = 23 mod 24
              omega
            · -- e is odd, f is odd => 2 - 2 = 2 => 0 = 2 mod 3
              have h_zmod3 : (q : ZMod 3) ^ f - (p : ZMod 3) ^ e = 2 := by
                have h_ge : q ^ f ≥ p ^ e := by omega
                have h_cast : ((q ^ f - p ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h
                rw [Nat.cast_sub h_ge] at h_cast
                push_cast at h_cast
                exact h_cast
              have hp2 : (p : ZMod 3) = 2 := by
                have : p % 3 = 2 := hp3_val
                have h_cast : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
                rw [h_cast, this]
                rfl
              have hq2 : (q : ZMod 3) = 2 := by
                have : q % 3 = 2 := hq3_val

    pillai_diff_two_code = fix_semicolons(pillai_diff_two_code)

    old_block = """                      have hq1 : (q : ZMod 3) = 1 := by
                        have : q % 3 = 1 := hq3_val
                        have h_cast : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
                        rw [h_cast, this]
                        rfl
                      have h_zmod_local : (q : ZMod 3) ^ f - (5 : ZMod 3) ^ e = 2 := h_zmod
                      have h5e : (5 : ZMod 3) ^ e = 2 := by
                        have : (5 : ZMod 3) = 2 := rfl
                        rw [this]
                        have h_eq : e = 2 * (e / 2) + 1 := by omega
                        rw [h_eq]
                        have : (2 : ZMod 3) ^ (2 * (e / 2) + 1) = ((2 : ZMod 3) ^ 2) ^ (e / 2) * 2 := by
                          rw [pow_succ, pow_mul]
                        rw [this]
                        have : (2 : ZMod 3) ^ 2 = 1 := rfl


theorem oeis_365416_conjecture_0 :
  ∀ k : ℕ,
    (IsCompositePrimePow (2 * k - 1) ∧ IsCompositePrimePow (2 * k + 1)) ↔ k = 13 := by
  intro k
  constructor
  · intro h
    by_cases hk13 : k = 13
    · exact hk13
    · exfalso
      by_cases hk_lt : k < 14
      · interval_cases k
        · exact not_isCompositePrimePow_of_lt_four 0 (by decide) h.1
        · exact not_isCompositePrimePow_of_lt_four 1 (by decide) h.1
        · exact not_isCompositePrimePow_of_lt_four 3 (by decide) h.1
        · exact not_isCompositePrimePow_of_prime 5 (by decide) h.1
        · exact not_isCompositePrimePow_of_prime 7 (by decide) h.1
        · exact not_isCompositePrimePow_of_prime 11 (by decide) h.2
        · exact not_isCompositePrimePow_of_prime 11 (by decide) h.1
        · exact not_isCompositePrimePow_of_prime 13 (by decide) h.1
        · exact not_isCompositePrimePow_of_prime 17 (by decide) h.2
        · exact not_isCompositePrimePow_of_prime 17 (by decide) h.1
        · exact not_isCompositePrimePow_of_prime 19 (by decide) h.1
        · exact not_isCompositePrimePow_of_prime 23 (by decide) h.2
        · exact not_isCompositePrimePow_of_prime 23 (by decide) h.1
        · exact hk13 rfl
      · have h_ge : k ≥ 14 := by omega
        rcases h with ⟨h1, h2⟩
        rcases h1 with ⟨p, e, hp, he, hp_eq⟩
        rcases h2 with ⟨q, f, hq, hf, hq_eq⟩
        have h_sub : q ^ f - p ^ e = 2 := by omega
        have h_pillai := pillai_diff_two p q e f hp hq he hf h_sub
        have hp_eq5 : p = 5 := h_pillai.1
        have he_eq2 : e = 2 := h_pillai.2.1
        have : 2 * k - 1 = 25 := by
          calc 2 * k - 1 = p ^ e := hp_eq.symm
          _ = 5 ^ 2 := by rw [hp_eq5, he_eq2]
          _ = 25 := by rfl
        omega
  · intro h
    subst h
    constructor
    · use 5, 2
      refine ⟨by decide, by decide, by rfl⟩
    · use 3, 3
      refine ⟨by decide, by decide, by rfl⟩

#print axioms oeis_365416_conjecture_0

