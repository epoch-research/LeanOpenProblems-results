import FormalConjectures.Util.ProblemImports

open Nat

lemma lt_pow_self (e : ℕ) : e < 2 ^ e := by
  induction e with
  | zero => decide
  | succ e ih =>
    have h_pow : 2 ^ (e + 1) = 2 ^ e + 2 ^ e := by ring
    omega

lemma pow_succ_sub_pow_ge (k f : ℕ) (hf : 2 ≤ f) : k ^ f + f * k ^ (f - 1) ≤ (k + 1) ^ f := by
  induction f, hf using Nat.le_induction with
  | base =>
    have : 2 - 1 = 1 := rfl
    rw [this]
    ring_nf
    omega
  | succ f hf ih =>
    have h1 : (k + 1) ^ (f + 1) = (k + 1) ^ f * (k + 1) := by ring
    have h2 : (k + 1) ^ f * (k + 1) ≥ (k ^ f + f * k ^ (f - 1)) * (k + 1) := Nat.mul_le_mul_right (k + 1) ih
    have h3 : (k ^ f + f * k ^ (f - 1)) * (k + 1) = k ^ (f + 1) + (f + 1) * k ^ f + f * k ^ (f - 1) := by
      have h_pow1 : k ^ (f - 1) * k = k ^ f := by
        have : k ^ (f - 1) * k = k ^ (f - 1) * k ^ 1 := by rw [pow_one]
        rw [this, ← pow_add]
        have : f - 1 + 1 = f := Nat.sub_add_cancel (by omega)
        rw [this]
      have h_pow2 : k ^ f * k = k ^ (f + 1) := by rw [pow_succ]
      calc (k ^ f + f * k ^ (f - 1)) * (k + 1) = k ^ f * k + k ^ f + f * (k ^ (f - 1) * k) + f * k ^ (f - 1) := by ring
        _ = k ^ (f + 1) + (f + 1) * k ^ f + f * k ^ (f - 1) := by
          rw [h_pow1, h_pow2]
          ring
    have h4 : k ^ (f + 1) + (f + 1) * k ^ f + f * k ^ (f - 1) ≥ k ^ (f + 1) + (f + 1) * k ^ f := by omega
    calc (k + 1) ^ (f + 1) = (k + 1) ^ f * (k + 1) := h1
      _ ≥ (k ^ f + f * k ^ (f - 1)) * (k + 1) := h2
      _ = k ^ (f + 1) + (f + 1) * k ^ f + f * k ^ (f - 1) := h3
      _ ≥ k ^ (f + 1) + (f + 1) * k ^ f := h4

lemma exists_largest_power (f target : ℕ) (hf : 0 < f) : ∃ A, A ^ f ≤ target ∧ target < (A + 1) ^ f := by
  induction target with
  | zero =>
    use 0
    rw [zero_pow hf.ne']
    refine ⟨by decide, ?_⟩
    have h_pow : (0 + 1) ^ f = 1 := by
      have : 0 + 1 = 1 := by rfl
      rw [this, one_pow]
    omega
  | succ n ih =>
    rcases ih with ⟨A, h1, h2⟩
    have h_cases : n + 1 < (A + 1) ^ f ∨ (A + 1) ^ f = n + 1 := by omega
    rcases h_cases with h_lt | h_eq
    · use A
      omega
    · use A + 1
      refine ⟨by omega, ?_⟩
      have h_lt : (A + 1) ^ f < (A + 1 + 1) ^ f := Nat.pow_lt_pow_left (by omega) hf.ne'
      omega

lemma no_solution_if_e_ge_f_add_one {p e q f : ℕ} (hp : p.Prime) (hq : q.Prime) (he : 1 < e) (hf : 1 < f) (h : q ^ f = p ^ e + 2) (hef : e ≥ f + 1) (hp3 : 3 ≤ p) : False := by
  have hf_pos : 0 < f := by omega
  obtain ⟨A, hA1, hA2⟩ := exists_largest_power f (p ^ e) hf_pos
  have h_A_pos : 2 ≤ A := by
    by_contra h_lt
    have : A ≤ 1 := by omega
    interval_cases A
    · -- A = 0
      have : p ^ e < 1 ^ f := by
        have : (0 : ℕ) + 1 = 1 := rfl
        rw [this] at hA2
        exact hA2
      rw [one_pow] at this
      have hp_pow_ge : p ^ e ≥ 27 := by
        calc p ^ e ≥ 3 ^ e := Nat.pow_le_pow_left hp3 e
          _ ≥ 3 ^ 3 := Nat.pow_le_pow_right (by decide) (by omega)
          _ = 27 := rfl
      omega
    · -- A = 1
      have : p ^ e < 2 ^ f := by
        have : (1 : ℕ) + 1 = 2 := rfl
        rw [this] at hA2
        exact hA2
      have hp_pow_ge : p ^ e ≥ 2 ^ (f + 1) := by
        calc p ^ e ≥ 2 ^ e := Nat.pow_le_pow_left hp.two_le e
          _ ≥ 2 ^ (f + 1) := Nat.pow_le_pow_right (by decide) hef
      have h_lt_2 : 2 ^ (f + 1) > 2 ^ f := Nat.pow_lt_pow_right (by decide) (by omega)
      omega
  have h_ge2 : 4 ≤ f * A ^ (f - 1) := by
    have hf_ge : 2 ≤ f := hf
    have hk_ge1 : A ^ 1 ≤ A ^ (f - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hk_ge2 : A ^ 1 = A := by ring
    have hk_ge3 : A ≤ A ^ (f - 1) := by omega
    calc 4 = 2 * 2 := rfl
      _ ≤ 2 * A := Nat.mul_le_mul_left 2 h_A_pos
      _ ≤ f * A ^ (f - 1) := Nat.mul_le_mul hf_ge hk_ge3
  have h_diff_ge : A ^ f + f * A ^ (f - 1) ≤ (A + 1) ^ f := pow_succ_sub_pow_ge A f hf
  generalize h_term : f * A ^ (f - 1) = T at h_ge2 h_diff_ge
  have h_A1_ge : A ^ f + 4 ≤ (A + 1) ^ f := Nat.le_trans (Nat.add_le_add_left h_ge2 (A ^ f)) h_diff_ge
  have h_cases : A ^ f = p ^ e ∨ A ^ f < p ^ e := Nat.eq_or_lt_of_le hA1
  rcases h_cases with h_eq | h_lt
  · have h_qf_eq : q ^ f = A ^ f + 2 := by omega
    have h_A1_ge2 : A ^ f + 4 ≤ (A + 1) ^ f := h_A1_ge
    have h_lt1 : q ^ f < (A + 1) ^ f := by omega
    have h_q_gt : q > A := by
      by_contra h_le
      have : q ≤ A := not_lt.mp h_le
      have : q ^ f ≤ A ^ f := Nat.pow_le_pow_left this f
      omega
    have : q ≥ A + 1 := h_q_gt
    have : q ^ f ≥ (A + 1) ^ f := Nat.pow_le_pow_left this f
    omega
  · have h_q_lt_A1 : q ^ f < (A + 1) ^ f := by
      have h_lt_le : A ^ f + 1 ≤ p ^ e := h_lt
      omega
    have h_q_le_A : q ≤ A := by
      by_contra h_gt
      have : q ≥ A + 1 := by omega
      have : q ^ f ≥ (A + 1) ^ f := Nat.pow_le_pow_left this f
      omega
    have h_qf_le_Af : q ^ f ≤ A ^ f := Nat.pow_le_pow_left h_q_le_A f
    have h_Af_lt_qf : A ^ f < q ^ f := by omega
    omega

lemma no_solution_if_f_ge_e_add_one {p e q f : ℕ} (hp : p.Prime) (hq : q.Prime) (he : 1 < e) (hf : 1 < f) (h : q ^ f = p ^ e + 2) (hfe : f ≥ e + 1) (hq3 : 3 ≤ q) : False := by
  have he_pos : 0 < e := by omega
  obtain ⟨B, hB1, hB2⟩ := exists_largest_power e (q ^ f) he_pos
  have h_B_pos : 2 ≤ B := by
    by_contra h_lt
    have : B ≤ 1 := by omega
    interval_cases B
    · -- B = 0
      have : q ^ f < 1 ^ e := by
        have : (0 : ℕ) + 1 = 1 := rfl
        rw [this] at hB2
        exact hB2
      rw [one_pow] at this
      have hq_pow_ge : q ^ f ≥ 9 := by
        calc q ^ f ≥ 3 ^ f := Nat.pow_le_pow_left hq3 f
          _ ≥ 3 ^ 2 := Nat.pow_le_pow_right (by decide) hf
          _ = 9 := rfl
      omega
    · -- B = 1
      have : q ^ f < 2 ^ e := by
        have : (1 : ℕ) + 1 = 2 := rfl
        rw [this] at hB2
        exact hB2
      have hq_pow_ge : q ^ f ≥ 2 ^ (e + 1) := by
        calc q ^ f ≥ 3 ^ f := Nat.pow_le_pow_left hq3 f
          _ ≥ 3 ^ (e + 1) := Nat.pow_le_pow_right (by decide) hfe
          _ ≥ 2 ^ (e + 1) := Nat.pow_le_pow_left (by decide) (e + 1)
      have h_lt_2 : 2 ^ (e + 1) > 2 ^ e := Nat.pow_lt_pow_right (by decide) (by omega)
      omega
  have h_ge2 : 4 ≤ e * B ^ (e - 1) := by
    have he_ge : 2 ≤ e := he
    have hk_ge1 : B ^ 1 ≤ B ^ (e - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hk_ge2 : B ^ 1 = B := by ring
    have hk_ge3 : B ≤ B ^ (e - 1) := by omega
    calc 4 = 2 * 2 := rfl
      _ ≤ 2 * B := Nat.mul_le_mul_left 2 h_B_pos
      _ ≤ e * B ^ (e - 1) := Nat.mul_le_mul he_ge hk_ge3
  have h_diff_ge : B ^ e + e * B ^ (e - 1) ≤ (B + 1) ^ e := pow_succ_sub_pow_ge B e he
  generalize h_term : e * B ^ (e - 1) = T at h_ge2 h_diff_ge
  have h_B1_ge : B ^ e + 4 ≤ (B + 1) ^ e := Nat.le_trans (Nat.add_le_add_left h_ge2 (B ^ e)) h_diff_ge
  have h_cases : B ^ e = q ^ f ∨ B ^ e < q ^ f := Nat.eq_or_lt_of_le hB1
  rcases h_cases with h_eq | h_lt
  · have h_pe_eq : p ^ e = B ^ e - 2 := by omega
    have h_B1_ge2 : B ^ e + 4 ≤ (B + 1) ^ e := h_B1_ge
    have h_lt1 : p ^ e < (B + 1) ^ e := by omega
    have h_p_gt : p > B := by
      by_contra h_le
      have : p ≤ B := not_lt.mp h_le
      have : p ^ e ≤ B ^ e := Nat.pow_le_pow_left this e
      omega
    have : p ≥ B + 1 := h_p_gt
    have : p ^ e ≥ (B + 1) ^ e := Nat.pow_le_pow_left this e
    omega
  · have h_pe_lt_B1 : p ^ e < (B + 1) ^ e := by
      have h_lt_le : B ^ e + 1 ≤ q ^ f := h_lt
      omega
    have h_p_le_B : p ≤ B := by
      by_contra h_gt
      have : p ≥ B + 1 := by omega
      have : p ^ e ≥ (B + 1) ^ e := Nat.pow_le_pow_left this e
      omega
    have h_pe_le_Be : p ^ e ≤ B ^ e := Nat.pow_le_pow_left h_p_le_B e
    have h_Be_lt_pe : B ^ e < p ^ e := by omega
    omega
