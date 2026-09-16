import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma padicValNat_add_of_not_dvd (p a b : ℕ) [Fact p.Prime] (h : p ∣ a) (h2 : ¬ p ∣ b) :
  padicValNat p (a + b) = 0 := by
  have : ¬ p ∣ a + b := by
    intro hdvd
    have : p ∣ (a + b) - a := Nat.dvd_sub hdvd h
    have h_eq : (a + b) - a = b := by omega
    rw [h_eq] at this
    exact h2 this
  exact padicValNat.eq_zero_of_not_dvd this

lemma padicValNat_pM_add_k (p M k : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hk1 : 1 ≤ k) (hk2 : k ≤ p * (p - 2))
  (hM : p ∣ M - 1) (hM_ge : 1 ≤ M) : padicValNat p (p * M + k) = if p ∣ k then 1 else 0 := by
  split_ifs with h
  · obtain ⟨j, hj⟩ := h
    have hj1 : 1 ≤ j := by
      rcases j with _ | j
      · omega
      · omega
    have hj2 : j ≤ p - 2 := by
      have : p * j ≤ p * (p - 2) := by omega
      exact Nat.le_of_mul_le_mul_left this (by omega)
    have : p * M + k = p * (M + j) := by
      rw [hj]
      ring
    rw [this]
    have h_ne : M + j ≠ 0 := by
      have : 1 ≤ M + j := by omega
      omega
    have hp_ne : p ≠ 0 := by omega
    rw [padicValNat.mul hp_ne h_ne]
    have hp_prime : p.Prime := Fact.out
    have : padicValNat p p = 1 := padicValNat.self hp_prime.one_lt
    rw [this]
    have h_not_dvd : ¬ p ∣ M + j := by
      intro hdvd
      have hM_mod : p ∣ M - 1 := hM
      have H2 : p ∣ (M - 1) + (j + 1) := by
        have H3 : (M - 1) + (j + 1) = M + j := by omega
        rw [H3]
        exact hdvd
      have H4 : p ∣ ((M - 1) + (j + 1)) - (M - 1) := Nat.dvd_sub H2 hM_mod
      have H5 : ((M - 1) + (j + 1)) - (M - 1) = j + 1 := by omega
      rw [H5] at H4
      have H6 : j + 1 < p := by omega
      have H7 : j + 1 = 0 := Nat.eq_zero_of_dvd_of_lt H4 H6
      omega
    have : padicValNat p (M + j) = 0 := padicValNat.eq_zero_of_not_dvd h_not_dvd
    omega
  · apply padicValNat_add_of_not_dvd
    · exact dvd_mul_right p M
    · exact h
