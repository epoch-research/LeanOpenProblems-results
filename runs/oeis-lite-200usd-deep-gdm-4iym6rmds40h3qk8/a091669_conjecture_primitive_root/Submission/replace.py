import sys

with open("/workspace/leanproject/Submission/temp.lean", "r") as f:
    content = f.read()

idx = content.find("lemma prime_of_dvd")
if idx == -1:
    print("Could not find lemma prime_of_dvd")
    sys.exit(1)

header_and_helpers = content[:idx]

new_prime_of_dvd = """lemma prime_of_dvd (n : ℕ) (hn : n > 2) (h_dvd : n ∣ (a (n - 1) + 2 ^ (n - 2))) :
  Nat.Prime n := by
  by_contra hnp
  have hn1 : n > 1 := by omega
  rcases exists_odd_prime_factor_or_power_of_two n hn1 with ⟨k, rfl⟩ | ⟨p, pp, hp2, hp_dvd_n⟩
  · have hk : k ≥ 2 := by
      by_contra hc
      have : k = 0 ∨ k = 1 := by omega
      rcases this with rfl | rfl
      · simp at hn
      · simp at hn
    have h_exact := a_exact (2 ^ k) hn
    have h_padic_eq : padicValNat 2 (a (2 ^ k - 1) * (2 ^ k - 1).factorial) =
        padicValNat 2 (2 ^ (2 ^ k - 2) * (Finset.Ico 1 (2 ^ k - 1)).prod (fun k => 2 ^ k - 1)) := by
      rw [h_exact]
    have h_rhs_eq : padicValNat 2 (2 ^ (2 ^ k - 2) * (Finset.Ico 1 (2 ^ k - 1)).prod (fun k => 2 ^ k - 1)) = 2 ^ k - 2 := by
      have h_mul : padicValNat 2 (2 ^ (2 ^ k - 2) * (Finset.Ico 1 (2 ^ k - 1)).prod (fun k => 2 ^ k - 1)) =
          padicValNat 2 (2 ^ (2 ^ k - 2)) + padicValNat 2 ((Finset.Ico 1 (2 ^ k - 1)).prod (fun k => 2 ^ k - 1)) := by
        apply padicValNat.mul
        · positivity
        · apply Finset.prod_ne_zero_iff.mpr
          intro m hm
          rw [Finset.mem_Ico] at hm
          have hm1 : m ≥ 1 := hm.1
          have h2m : 2 ^ m ≥ 2 := by
            have : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hm1
            exact this
          omega
      rw [h_mul]
      have h_pow : padicValNat 2 (2 ^ (2 ^ k - 2)) = 2 ^ k - 2 := padicValNat.prime_pow (2 ^ k - 2)
      have h_prod_padic : padicValNat 2 ((Finset.Ico 1 (2 ^ k - 1)).prod (fun k => 2 ^ k - 1)) = 0 := by
        apply padicValNat.eq_zero_of_not_dvd
        intro h_dvd_odd
        have hp_two_prime : Nat.Prime 2 := Nat.prime_two
        have hp_prime_algebraic : _root_.Prime 2 := Nat.Prime.prime hp_two_prime
        rw [hp_prime_algebraic.dvd_prod_iff] at h_dvd_odd
        have ⟨m, hm_ico, hm_dvd⟩ := h_dvd_odd
        rw [Finset.mem_Ico] at hm_ico
        have : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
        have h_sub_dvd : 2 ∣ 2 ^ m - (2 ^ m - 1) := Nat.dvd_sub (by
          have : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hm_ico.1
          omega) this hm_dvd
        have h_diff : 2 ^ m - (2 ^ m - 1) = 1 := by
          have : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hm_ico.1
          omega
        rw [h_diff] at h_sub_dvd
        contradiction
      rw [h_pow, h_prod_padic, add_zero]
    have h_lhs_eq : padicValNat 2 (a (2 ^ k - 1) * (2 ^ k - 1).factorial) =
        padicValNat 2 (a (2 ^ k - 1)) + padicValNat 2 (2 ^ k - 1).factorial := by
      apply padicValNat.mul
      · intro hc
        have h_rhs_ne := rhs_ne_zero (2 ^ k) hn
        rw [hc, zero_mul] at h_exact
        exact h_rhs_ne h_exact.symm
      · exact factorial_ne_zero (2 ^ k - 1)
    rw [h_lhs_eq, h_rhs_eq] at h_padic_eq
    rw [padicValNat_two_factorial_power k hk] at h_padic_eq
    have h_padic_a : padicValNat 2 (a (2 ^ k - 1)) = k - 1 := by
      have h_ge : 2 ^ k ≥ 3 := by
        have := two_pow_ge_succ k
        omega
      generalize ht : 2 ^ k = tk at h_ge h_padic_eq ⊢
      omega
    have hp_dvd_sum : 2 ^ k ∣ a (2 ^ k - 1) + 2 ^ (2 ^ k - 2) := h_dvd
    have h_pow_le : k ≤ 2 ^ k - 2 := by
      have := two_pow_ge_succ k
      omega
    have hp_two_dvd_a : 2 ^ k ∣ a (2 ^ k - 1) := by
      have h_div_pow : 2 ^ k ∣ 2 ^ (2 ^ k - 2) := by
        use 2 ^ (2 ^ k - 2 - k)
        rw [← pow_add]
        congr 1
        omega
      have h_sub : a (2 ^ k - 1) = (a (2 ^ k - 1) + 2 ^ (2 ^ k - 2)) - 2 ^ (2 ^ k - 2) := by omega
      rw [h_sub]
      have h_le_add : 2 ^ (2 ^ k - 2) ≤ a (2 ^ k - 1) + 2 ^ (2 ^ k - 2) := Nat.le_add_left _ _
      exact Nat.dvd_sub h_le_add hp_dvd_sum h_div_pow
    have h_val_a_ge : padicValNat 2 (a (2 ^ k - 1)) ≥ k := by
      have h_ne : a (2 ^ k - 1) ≠ 0 := by
        intro hc
        have h_rhs_ne := rhs_ne_zero (2 ^ k) hn
        rw [hc, zero_mul] at h_exact
        exact h_rhs_ne h_exact.symm
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact (padicValNat_dvd_iff_le h_ne).mp hp_two_dvd_a
    omega
  · haveI : Fact p.Prime := ⟨pp⟩
    have hp_dvd_sum : p ∣ a (n - 1) + 2 ^ (n - 2) := dvd_trans hp_dvd_n h_dvd
    have h_exact := a_exact n hn
    have hp_not_dvd_a : ¬ p ∣ a (n - 1) := by
      intro hc
      have h_sub : 2 ^ (n - 2) = a (n - 1) + 2 ^ (n - 2) - a (n - 1) := by
        generalize ha : a (n - 1) = X
        generalize h_pow : 2 ^ (n - 2) = Y
        omega
      have : p ∣ a (n - 1) + 2 ^ (n - 2) - a (n - 1) := by
        have h_le_add2 : a (n - 1) ≤ a (n - 1) + 2 ^ (n - 2) := Nat.le_add_right _ _
        exact Nat.dvd_sub h_le_add2 hp_dvd_sum hc
      rw [← h_sub] at this
      haveI : Fact p.Prime := ⟨pp⟩
      rw [(_root_.Prime.dvd_pow_iff_dvd (Nat.Prime.prime pp)) (by omega)] at this
      · exact hp2 (by
          have : p ∣ 2 := this
          have : p ≤ 2 := Nat.le_of_dvd (by decide) this
          have : p > 1 := pp.one_lt
          omega)
    have hp_padic_a : padicValNat p (a (n - 1)) = 0 := padicValNat.eq_zero_of_not_dvd hp_not_dvd_a
    have h_padic_eq : padicValNat p (a (n - 1) * (n - 1).factorial) =
        padicValNat p (2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := by
      rw [h_exact]
    have h_rhs_eq : padicValNat p (2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) =
        ∑ k ∈ Finset.Ico 1 (n - 1), padicValNat p (2 ^ k - 1) := by
      have h_mul : padicValNat p (2 ^ (n - 2) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) =
          padicValNat p (2 ^ (n - 2)) + padicValNat p ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := by
        apply padicValNat.mul
        · positivity
        · apply Finset.prod_ne_zero_iff.mpr
          intro k hk
          rw [Finset.mem_Ico] at hk
          have hk1 : k ≥ 1 := hk.1
          have h2k : 2 ^ k ≥ 2 := by
            have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk1
            exact this
          omega
      rw [h_mul]
      have h_pow : padicValNat p (2 ^ (n - 2)) = 0 := by
        apply padicValNat.eq_zero_of_not_dvd
        intro hc
        haveI : Fact p.Prime := ⟨pp⟩
        rw [(_root_.Prime.dvd_pow_iff_dvd (Nat.Prime.prime pp)) (by omega)] at hc
        · exact hp2 (by
            have : p ∣ 2 := hc
            have : p ≤ 2 := Nat.le_of_dvd (by decide) this
            have : p > 1 := pp.one_lt
            omega)
      rw [h_pow, zero_add]
      rw [padicValNat_prod_apply pp]
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hk1 : k ≥ 1 := hk.1
      have h2k : 2 ^ k ≥ 2 := by
        have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk1
        exact this
      omega
    have h_lhs_eq : padicValNat p (a (n - 1) * (n - 1).factorial) =
        padicValNat p (a (n - 1)) + padicValNat p (n - 1).factorial := by
      apply padicValNat.mul
      · intro hc
        have h_rhs_ne := rhs_ne_zero n hn
        rw [hc, zero_mul] at h_exact
        exact h_rhs_ne h_exact.symm
      · exact factorial_ne_zero (n - 1)
    rw [h_lhs_eq, hp_padic_a, zero_add] at h_padic_eq
    rcases hp_dvd_n with ⟨m, rfl⟩
    have hm : m ≥ 2 := by
      cases m
      · exfalso; omega
      · case succ m' =>
        cases m'
        · exfalso
          rw [Nat.mul_one] at hnp
          exact hnp pp
        · omega
    by_cases h_cases : p ≤ m
    · have h_ord_le := order_le_p_sub_one p pp hp2
      have h_mul_le : orderOf (2 : ZMod p) * p ≤ (p - 1) * p := Nat.mul_le_mul_right p h_ord_le
      have h_ineq : orderOf (2 : ZMod p) * p ≤ p * m - 2 := by
        have hp_ge_3 : p ≥ 3 := by
          have : p > 1 := pp.one_lt
          omega
        have h_prod : (p - 1) * p = p * p - p := by
          rw [Nat.sub_mul, one_mul, mul_comm]
        have h_sub_le : p * p - p ≤ p * m - 2 := by
          have : p * p ≤ p * m := Nat.mul_le_mul_right p h_cases
          omega
        omega
      have h_sum_ge := sum_padicVal_strict_ge_div_order p (p * m - 1) pp hp2 (by
        have h_sub_eq : p * m - 1 - 1 = p * m - 2 := by omega
        rw [h_sub_eq]
        exact h_ineq)
      have h_le1 := padicVal_factorial_le_div_order p (p * m - 1) pp hp2 (by omega)
      have h_sub_eq : p * m - 1 - 1 = p * m - 2 := by omega
      rw [h_sub_eq] at h_le1
      rw [h_padic_eq] at h_le1
      generalize h_sum_val : ∑ k ∈ Finset.Ico 1 (p * m - 1), padicValNat p (2 ^ k - 1) = S at h_sum_ge h_le1 ⊢
      generalize h_div_eq : (p * m - 2) / orderOf (2 : ZMod p) = K at h_sum_ge h_le1
      omega
    · have hpm : p > m := by omega
      have h_le_fact := padicValNat_factorial_le_m_sub_one p m pp hp2 hm hpm
      have h_sum_ge : ∑ k ∈ Finset.Ico 1 (p * m - 1), padicValNat p (2 ^ k - 1) ≥ m := by
        have h_sum_ge_div := sum_padicVal_ge_div_order p (p * m - 1) pp hp2
        have h_sub_eq : p * m - 1 - 1 = p * m - 2 := by omega
        rw [h_sub_eq] at h_sum_ge_div
        have h_ord_pos : orderOf (2 : ZMod p) > 0 := by
          have hp_gt : p > 2 := by
            have : p > 1 := pp.one_lt
            omega
          exact orderOf_two_pos p hp_gt pp
        have h_ord_le := order_le_p_sub_one p pp hp2
        have h_mul_le_m : orderOf (2 : ZMod p) * m ≤ (p - 1) * m := Nat.mul_le_mul_right m h_ord_le
        have h_sub_le : (p - 1) * m ≤ p * m - 2 := by
          have h_dist : (p - 1) * m = p * m - m := by
            rw [Nat.sub_mul, one_mul]
          rw [h_dist]
          omega
        have h_trans : orderOf (2 : ZMod p) * m ≤ p * m - 2 := le_trans h_mul_le_m h_sub_le
        have h_div_ge : m ≤ (p * m - 2) / orderOf (2 : ZMod p) := by
          rw [Nat.le_div_iff_mul_le h_ord_pos]
          rw [mul_comm]
          exact h_trans
        omega
      rw [h_padic_eq] at h_le_fact
      clear h_ord_pos h_ord_le h_mul_le_m h_sub_le h_trans h_exact hp_dvd_sum hp_padic_a h_lhs_eq h_rhs_eq hp_not_dvd_a h_padic_eq
      omega
"""

with open("/workspace/leanproject/Submission/temp.lean", "w") as f:
    f.write(header_and_helpers + new_prime_of_dvd)

print("Successfully updated temp.lean")
