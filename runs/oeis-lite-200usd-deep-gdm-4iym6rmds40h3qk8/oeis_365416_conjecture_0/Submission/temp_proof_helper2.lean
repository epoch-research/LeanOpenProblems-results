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
