import FormalConjectures.Util.ProblemImports

open Nat

def IsCompositePrimePow (m : ℕ) : Prop :=
  ∃ (p e : ℕ), Nat.Prime p ∧ 1 < e ∧ p ^ e = m

lemma lt_pow_self (e : ℕ) : e < 2 ^ e := by
  induction e with
  | zero => decide
  | succ e ih =>
    have h_pow : 2 ^ (e + 1) = 2 ^ e + 2 ^ e := by ring
    omega

lemma IsCompositePrimePow_iff_bounded (m : ℕ) :
  IsCompositePrimePow m ↔ ∃ p < m, ∃ e < m, Nat.Prime p ∧ 1 < e ∧ p ^ e = m := by
  constructor
  · rintro ⟨p, e, hp, he, rfl⟩
    have hp2 : 2 ≤ p := hp.two_le
    have he2 : 2 ≤ e := he
    have hp_lt : p < p ^ e := by
      calc p < p * 2 := by omega
        _ ≤ p * p := Nat.mul_le_mul_left p hp2
        _ = p ^ 2 := by ring
        _ ≤ p ^ e := Nat.pow_le_pow_right (by omega) he2
    have he_lt : e < p ^ e := by
      calc e < 2 ^ e := lt_pow_self e
        _ ≤ p ^ e := Nat.pow_le_pow_left hp2 e
    exact ⟨p, hp_lt, e, he_lt, hp, he, rfl⟩
  · rintro ⟨p, _, e, _, hp, he, rfl⟩
    exact ⟨p, e, hp, he, rfl⟩

lemma test_conjecture_lt_14 (k : ℕ) (hk : k < 14) :
    (IsCompositePrimePow (2 * k - 1) ∧ IsCompositePrimePow (2 * k + 1)) ↔ k = 13 := by
  constructor
  · intro h
    interval_cases k <;> try rfl
    all_goals
      have h1 := h.1
      have h2 := h.2
      simp only [IsCompositePrimePow_iff_bounded] at h1 h2
      revert h1 h2
      decide
  · rintro rfl
    constructor
    · use 5, 2
      refine ⟨by decide, by decide, by rfl⟩
    · use 3, 3
      refine ⟨by decide, by decide, by rfl⟩

lemma pow_succ_sub_pow_ge (k f : ℕ) (hf : 2 ≤ f) : (k + 1) ^ f ≥ k ^ f + f * k ^ (f - 1) := by
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

lemma q_gt_p_implies_f_lt_e {p e q f : ℕ} (hp : p.Prime) (hq : q.Prime) (he : 1 < e) (hf : 1 < f) (h : q ^ f - p ^ e = 2) (hqp : p < q) : f < e := by
  by_contra h_ge
  have h_le : e ≤ f := not_lt.mp h_ge
  have hp_le : p ≤ q - 1 := by omega
  have hq_pos : q > 0 := hq.pos
  have hk : q - 1 ≥ 2 := by
    have : q ≥ 3 := by
      have := hq.two_le
      have : p ≥ 2 := hp.two_le
      omega
    omega
  have hp_pow_le : p ^ e ≤ p ^ f := Nat.pow_le_pow_right hp.pos h_le
  have hp_pow_le_k : p ^ f ≤ (q - 1) ^ f := Nat.pow_le_pow_left hp_le f
  have hp_pow_le_q : p ^ e ≤ (q - 1) ^ f := Nat.le_trans hp_pow_le hp_pow_le_k
  have h_sub_ge : q ^ f - p ^ e ≥ q ^ f - (q - 1) ^ f := by omega
  have h_diff_ge : (q - 1 + 1) ^ f ≥ (q - 1) ^ f + f * (q - 1) ^ (f - 1) := pow_succ_sub_pow_ge (q - 1) f hf
  have h_eq : q - 1 + 1 = q := by omega
  rw [h_eq] at h_diff_ge
  have h_diff_ge_sub : q ^ f - (q - 1) ^ f ≥ f * (q - 1) ^ (f - 1) := by omega
  have h_ge2 : f * (q - 1) ^ (f - 1) ≥ 4 := by
    have hf_ge : f ≥ 2 := hf
    have hk_ge1 : (q - 1) ^ (f - 1) ≥ (q - 1) ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
    have hk_ge2 : (q - 1) ^ 1 = q - 1 := by ring
    have hk_ge3 : (q - 1) ^ (f - 1) ≥ q - 1 := by omega
    calc f * (q - 1) ^ (f - 1) ≥ 2 * (q - 1) := Nat.mul_le_mul hf_ge hk_ge3
      _ ≥ 2 * 2 := Nat.mul_le_mul_left 2 hk
      _ = 4 := rfl
  omega

lemma p_gt_q_implies_e_lt_f {p e q f : ℕ} (hp : p.Prime) (hq : q.Prime) (he : 1 < e) (hf : 1 < f) (h : q ^ f - p ^ e = 2) (hpq : q < p) : e < f := by
  by_contra h_ge
  have h_le : f ≤ e := not_lt.mp h_ge
  have hq_pow_le : q ^ f ≤ q ^ e := Nat.pow_le_pow_right hq.pos h_le
  have hp_gt : q ^ e < p ^ e := Nat.pow_lt_pow_left hpq (by omega)
  have h_lt : q ^ f < p ^ e := Nat.lt_of_le_of_lt hq_pow_le hp_gt
  omega

lemma no_solution_if_e_ge_f_add_one {p e q f : ℕ} (hp : p.Prime) (hq : q.Prime) (he : 1 < e) (hf : 1 < f) (h : q ^ f = p ^ e + 2) (hef : e ≥ f + 1) : False := by
  have hf_pos : 0 < f := by omega
  obtain ⟨A, hA1, hA2⟩ := exists_largest_power f (p ^ e) hf_pos
  have h_cases_div : f ∣ e ∨ ¬ f ∣ e := Classical.em (f ∣ e)
  rcases h_cases_div with ⟨j, rfl⟩ | h_not_div
  · -- f | e, so e = f * j. Since e >= f + 1 => j >= 2
    have hj : j ≥ 2 := by
      have : f * j ≥ f + 1 := by omega
      have : f * j > f * 1 := by omega
      omega
    have h_pow_eq : p ^ (f * j) = (p ^ j) ^ f := by ring
    have h_contra1 : (p ^ j) ^ f < q ^ f := by
      rw [← h_pow_eq]
      omega
    have h_contra2 : q ^ f < (p ^ j + 1) ^ f := by
      have h_diff_ge : (p ^ j + 1) ^ f ≥ (p ^ j) ^ f + f * (p ^ j) ^ (f - 1) := pow_succ_sub_pow_ge (p ^ j) f hf
      have h_ge2 : f * (p ^ j) ^ (f - 1) ≥ 8 := by
        have hf_ge : f ≥ 2 := hf
        have hk_ge1 : (p ^ j) ^ (f - 1) ≥ (p ^ j) ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
        have hk_ge2 : (p ^ j) ^ 1 = p ^ j := by ring
        have hk_ge3 : (p ^ j) ^ (f - 1) ≥ p ^ j := by omega
        have hpj_ge : p ^ j ≥ 4 := by
          calc p ^ j ≥ 2 ^ j := Nat.pow_le_pow_left hp.two_le j
            _ ≥ 2 ^ 2 := Nat.pow_le_pow_right (by decide) hj
            _ = 4 := rfl
        calc f * (p ^ j) ^ (f - 1) ≥ 2 * (p ^ j) := Nat.mul_le_mul hf_ge hk_ge3
          _ ≥ 2 * 4 := Nat.mul_le_mul_left 2 hpj_ge
          _ = 8 := rfl
      rw [h_pow_eq] at h_diff_ge
      omega
    have h_lt1 : p ^ j < q := Nat.pow_lt_pow_iff_left hf_pos.ne' |>.mp h_contra1
    have h_lt2 : q < p ^ j + 1 := Nat.pow_lt_pow_iff_left hf_pos.ne' |>.mp h_contra2
    omega
  · -- f does not divide e. So p^e is not a perfect f-th power.
    -- Thus A^f < p^e
    have hA1_lt : A ^ f < p ^ e := by
      by_contra h_ge
      have h_eq : A ^ f = p ^ e := Nat.le_antisymm hA1 (not_lt.mp h_ge)
      have h_div : f ∣ e := by
        -- since p is prime and A^f = p^e => f | e
        sorry
      contradiction
    have h_contra1 : A ^ f < q ^ f - 2 := by omega
    have h_contra2 : q ^ f - 2 < (A + 1) ^ f := by omega
    have h_diff_ge : (A + 1) ^ f ≥ A ^ f + f * A ^ (f - 1) := pow_succ_sub_pow_ge A f hf
    have hA_pos : A ≥ 2 := by
      by_contra h_lt
      have : A + 1 ≤ 2 := by omega
      have h_pow_le : (A + 1) ^ f ≤ 2 ^ f := Nat.pow_le_pow_left this f
      have hp_pow_ge : p ^ e ≥ 2 ^ (f + 1) := by
        calc p ^ e ≥ 2 ^ e := Nat.pow_le_pow_left hp.two_le e
          _ ≥ 2 ^ (f + 1) := Nat.pow_le_pow_right (by decide) hef
      have : 2 ^ (f + 1) = 2 * 2 ^ f := by ring
      omega
    have h_ge2 : f * A ^ (f - 1) ≥ 4 := by
      have hf_ge : f ≥ 2 := hf
      have hk_ge1 : A ^ (f - 1) ≥ A ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
      have hk_ge2 : A ^ 1 = A := by ring
      have hk_ge3 : A ^ (f - 1) ≥ A := by omega
      calc f * A ^ (f - 1) ≥ 2 * A := Nat.mul_le_mul hf_ge hk_ge3
        _ ≥ 2 * 2 := Nat.mul_le_mul_left 2 hA_pos
        _ = 4 := rfl
    have h_contra3 : (A + 1) ^ f > q ^ f := by
      calc (A + 1) ^ f ≥ A ^ f + f * A ^ (f - 1) := h_diff_ge
        _ ≥ A ^ f + 4 := by omega
        _ ≥ (q ^ f - 2) + 4 := by omega
        _ = q ^ f + 2 := by omega
        _ > q ^ f := by omega
    have h_qf_ge : q ^ f ≥ (A + 1) ^ f := by
      by_contra h_lt
      have h_le : q ^ f < (A + 1) ^ f := not_le.mp h_lt
      have h_le2 : q ^ f ≤ p ^ e := by
        have hA2_eq : p ^ e < (A + 1) ^ f := hA2
        omega
      omega
    omega

lemma no_solution_if_f_ge_e_add_one {p e q f : ℕ} (hp : p.Prime) (hq : q.Prime) (he : 1 < e) (hf : 1 < f) (h : q ^ f - p ^ e = 2) (hfe : f ≥ e + 1) : False := by
  have he_pos : 0 < e := by omega
  obtain ⟨B, hB1, hB2⟩ := exists_largest_power e (q ^ f) he_pos
  have h_cases_div : e ∣ f ∨ ¬ e ∣ f := Classical.em (e ∣ f)
  rcases h_cases_div with ⟨j, rfl⟩ | h_not_div
  · -- e | f, so f = e * j. Since f >= e + 1 => j >= 2
    have hj : j ≥ 2 := by
      have : e * j ≥ e + 1 := by omega
      have : e * j > e * 1 := by omega
      omega
    have h_pow_eq : q ^ (e * j) = (q ^ j) ^ e := by ring
    have h_contra1 : (q ^ j - 1) ^ e < p ^ e := by
      have h_eq : q ^ j - 1 + 1 = q ^ j := by omega
      have h_diff := pow_succ_sub_pow_ge (q ^ j - 1) e he
      rwa [h_eq] at h_diff
      have h_ge2 : e * (q ^ j - 1) ^ (e - 1) ≥ 16 := by
        have he_ge : e ≥ 2 := he
        have hk_ge1 : (q ^ j - 1) ^ (e - 1) ≥ (q ^ j - 1) ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
        have hk_ge2 : (q ^ j - 1) ^ 1 = q ^ j - 1 := by ring
        have hk_ge3 : (q ^ j - 1) ^ (e - 1) ≥ q ^ j - 1 := by omega
        have hqj_ge : q ^ j - 1 ≥ 8 := by
          calc q ^ j - 1 ≥ 3 ^ j - 1 := by
                have : q ^ j ≥ 3 ^ j := Nat.pow_le_pow_left (by omega) j
                omega
            _ ≥ 3 ^ 2 - 1 := by
                have : 3 ^ j ≥ 3 ^ 2 := Nat.pow_le_pow_right (by decide) hj
                omega
            _ = 8 := rfl
        calc e * (q ^ j - 1) ^ (e - 1) ≥ 2 * (q ^ j - 1) := Nat.mul_le_mul he_ge hk_ge3
          _ ≥ 2 * 8 := Nat.mul_le_mul_left 2 hqj_ge
          _ = 16 := rfl
      rw [h_pow_eq] at h_diff
      omega
    have h_contra2 : p ^ e < (q ^ j) ^ e := by
      rw [← h_pow_eq]
      omega
    have h_lt1 : q ^ j - 1 < p := Nat.pow_lt_pow_iff_left he_pos.ne' |>.mp h_contra1
    have h_lt2 : p < q ^ j := Nat.pow_lt_pow_iff_left he_pos.ne' |>.mp h_contra2
    omega
  · -- e does not divide f. So q^f is not a perfect e-th power.
    -- Thus B^e < q^f
    have hB1_lt : B ^ e < q ^ f := by
      by_contra h_ge
      have h_eq : B ^ e = q ^ f := Nat.le_antisymm hB1 (not_lt.mp h_ge)
      have h_div : e ∣ f := by
        -- since q is prime and B^e = q^f => e | f
        sorry
      contradiction
    have h_contra1 : B ^ e < p ^ e + 2 := by omega
    have h_contra2 : p ^ e + 2 < (B + 1) ^ e := by omega
    have h_diff_ge : (B + 1) ^ e ≥ B ^ e + e * B ^ (e - 1) := pow_succ_sub_pow_ge B e he
    have hB_pos : B ≥ 2 := by
      by_contra h_lt
      have : B + 1 ≤ 2 := by omega
      have h_pow_le : (B + 1) ^ e ≤ 2 ^ e := Nat.pow_le_pow_left this e
      have hq_pow_ge : q ^ f ≥ 2 ^ (e + 1) := by
        calc q ^ f ≥ 2 ^ f := Nat.pow_le_pow_left hq.two_le f
          _ ≥ 2 ^ (e + 1) := Nat.pow_le_pow_right (by decide) hfe
      have : 2 ^ (e + 1) = 2 * 2 ^ e := by ring
      omega
    have h_ge2 : e * B ^ (e - 1) ≥ 4 := by
      have he_ge : e ≥ 2 := he
      have hk_ge1 : B ^ (e - 1) ≥ B ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
      have hk_ge2 : B ^ 1 = B := by ring
      have hk_ge3 : B ^ (e - 1) ≥ B := by omega
      calc e * B ^ (e - 1) ≥ 2 * B := Nat.mul_le_mul he_ge hk_ge3
        _ ≥ 2 * 2 := Nat.mul_le_mul_left 2 hB_pos
        _ = 4 := rfl
    have h_contra3 : (B + 1) ^ e > p ^ e + 4 := by
      calc (B + 1) ^ e ≥ B ^ e + e * B ^ (e - 1) := h_diff_ge
        _ ≥ B ^ e + 4 := by omega
        _ ≥ (p ^ e + 2) + 4 := by omega
        _ = p ^ e + 6 := by omega
        _ > p ^ e + 4 := by omega
    omega
