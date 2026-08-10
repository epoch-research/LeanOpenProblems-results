import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 1000000
open Nat

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

lemma q_ne_p_of_diff_two (p q e f : ℕ) (hp : Nat.Prime p) (he : 1 < e) (h : q ^ f - p ^ e = 2) : q ≠ p := by
  intro hqp
  subst hqp
  have hq_pos : 0 < q := hp.pos
  by_cases hfe : f ≤ e
  · have : q ^ f ≤ q ^ e := Nat.pow_le_pow_right hq_pos hfe
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
    have hq_div : 2 ∣ q := Nat.Prime.dvd_of_dvd_pow hq h_even
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
      omega
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
      have : ¬ Nat.Prime 4 := by decide
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
      omega
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
      have : q ^ f ≥ 36 := by
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
