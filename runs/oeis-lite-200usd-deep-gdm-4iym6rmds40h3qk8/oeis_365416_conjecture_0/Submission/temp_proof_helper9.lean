import FormalConjectures.Util.ProblemImports

open Nat

lemma lt_pow_self (e : ℕ) : e < 2 ^ e := by
  induction e with
  | zero => decide
  | succ e ih =>
    have h_pow : 2 ^ (e + 1) = 2 ^ e + 2 ^ e := by ring
    omega

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

lemma no_solution_if_e_ge_f_add_one {p e q f : ℕ} (hp : p.Prime) (hq : q.Prime) (he : 1 < e) (hf : 1 < f) (h : q ^ f = p ^ e + 2) (hef : e ≥ f + 1) (hp7 : 7 ≤ p) : False := by
  have hf_pos : 0 < f := by omega
  obtain ⟨A, hA1, hA2⟩ := exists_largest_power f (p ^ e) hf_pos
  have hA_ge_p : A ≥ p := by
    by_contra h_lt
    have h_le : A + 1 ≤ p := by omega
    have h_pow_le : (A + 1) ^ f ≤ p ^ f := Nat.pow_le_pow_left h_le f
    have hp_pow_le : p ^ f ≤ p ^ (f + 1) := by
      have : p > 0 := hp.pos
      exact Nat.pow_le_pow_right this (by omega)
    have hp_pow_le2 : p ^ (f + 1) ≤ p ^ e := by
      have : p > 0 := hp.pos
      exact Nat.pow_le_pow_right this hef
    have h_contra : (A + 1) ^ f ≤ p ^ e := by
      calc (A + 1) ^ f ≤ p ^ f := h_pow_le
        _ ≤ p ^ (f + 1) := hp_pow_le
        _ ≤ p ^ e := hp_pow_le2
    omega
  have hA_ge7 : A ≥ 7 := by omega
  have h_diff_ge : (A + 1) ^ f ≥ A ^ f + f * A ^ (f - 1) := pow_succ_sub_pow_ge A f hf
  have h_ge2 : f * A ^ (f - 1) ≥ 14 := by
    have hf_ge : f ≥ 2 := hf
    have hk_ge1 : A ^ (f - 1) ≥ A ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
    have hk_ge2 : A ^ 1 = A := by ring
    have hk_ge3 : A ^ (f - 1) ≥ A := by omega
    calc f * A ^ (f - 1) ≥ 2 * A := Nat.mul_le_mul hf_ge hk_ge3
      _ ≥ 2 * 7 := Nat.mul_le_mul_left 2 hA_ge7
      _ = 14 := rfl
  have h_contra : (A + 1) ^ f > q ^ f := by
    calc (A + 1) ^ f ≥ A ^ f + f * A ^ (f - 1) := h_diff_ge
      _ ≥ p ^ e + 14 := by omega
      _ = q ^ f + 12 := by omega
  have h_qf_ge : q ^ f ≥ (A + 1) ^ f := by
    by_contra h_lt
    have h_le : q ^ f < (A + 1) ^ f := not_le.mp h_lt
    have h_le2 : q ^ f ≤ p ^ e := by
      have hA2_eq : p ^ e < (A + 1) ^ f := hA2
      omega
    omega
  omega
