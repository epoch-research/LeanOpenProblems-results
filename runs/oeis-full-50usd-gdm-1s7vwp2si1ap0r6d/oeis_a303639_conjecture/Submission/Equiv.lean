import FormalConjectures.Util.ProblemImports

open Nat BigOperators

def a_test (n : ℕ) : ℕ :=
  let B (k : ℕ) : ℕ := (2 * k + 1).choose k
  let R_sq := Finset.range (n.sqrt + 1)
  let R_binom := Finset.range (n + 1)
  R_sq.sum fun a =>
    R_sq.sum fun b =>
      R_binom.sum fun c =>
        R_binom.sum fun d =>
          if a ≤ b ∧ c ≤ d ∧ a ^ 2 + b ^ 2 + B c + B d = n then 1 else 0

lemma a_test_pos_iff (n : ℕ) :
    a_test n > 0 ↔ ∃ a_0 < n.sqrt + 1, ∃ b_0 < n.sqrt + 1, ∃ c_0 < n + 1, ∃ d_0 < n + 1,
    a_0 ≤ b_0 ∧ c_0 ≤ d_0 ∧ a_0 ^ 2 + b_0 ^ 2 + (2 * c_0 + 1).choose c_0 + (2 * d_0 + 1).choose d_0 = n := by
  unfold a_test
  dsimp
  change 0 < (∑ a ∈ Finset.range (n.sqrt + 1),
        ∑ b ∈ Finset.range (n.sqrt + 1),
          ∑ c ∈ Finset.range (n + 1),
            ∑ d ∈ Finset.range (n + 1),
              if a ≤ b ∧ c ≤ d ∧ a ^ 2 + b ^ 2 + (2 * c + 1).choose c + (2 * d + 1).choose d = n then 1 else 0) ↔ _
  rw [Finset.sum_pos_iff_of_nonneg]
  · simp only [Finset.mem_range]
    constructor
    · rintro ⟨a_0, ha0, h1⟩
      rw [Finset.sum_pos_iff_of_nonneg (by simp)] at h1
      rcases h1 with ⟨b_0, hb0, h2⟩
      rw [Finset.sum_pos_iff_of_nonneg (by simp)] at h2
      rcases h2 with ⟨c_0, hc0, h3⟩
      rw [Finset.sum_pos_iff_of_nonneg (by simp)] at h3
      rcases h3 with ⟨d_0, hd0, h4⟩
      rw [Finset.mem_range] at hb0 hc0 hd0
      split_ifs at h4 with h_eq
      · refine ⟨a_0, ha0, b_0, hb0, c_0, hc0, d_0, hd0, h_eq⟩
      · omega
    · rintro ⟨a_0, ha0, b_0, hb0, c_0, hc0, d_0, hd0, hab, hcd, h_eq⟩
      rw [← Finset.mem_range] at hb0 hc0 hd0
      refine ⟨a_0, ha0, ?_⟩
      rw [Finset.sum_pos_iff_of_nonneg (by simp)]
      refine ⟨b_0, hb0, ?_⟩
      rw [Finset.sum_pos_iff_of_nonneg (by simp)]
      refine ⟨c_0, hc0, ?_⟩
      rw [Finset.sum_pos_iff_of_nonneg (by simp)]
      refine ⟨d_0, hd0, ?_⟩
      split_ifs with h_cond
      · omega
      · exfalso
        exact h_cond ⟨hab, hcd, h_eq⟩
  · intro x hx
    exact zero_le'
