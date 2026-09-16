import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma padicValNat_le_one (p c d : ℕ) (hp : p.Prime) (h1 : 1 ≤ d) (h2 : d < p) :
  padicValNat p (p * (c * p + 1 + d)) = 1 := by
  have h_ne : c * p + 1 + d ≠ 0 := by omega
  rw [padicValNat.mul hp.ne_zero h_ne]
  have : padicValNat p p = 1 := padicValNat.self hp.ne_one
  rw [this]
  have h_not_dvd : ¬ (p ∣ c * p + 1 + d) := by
    intro hdvd
    have : p ∣ (1 + d) := by
      have h1 : p ∣ c * p := dvd_mul_left p c
      -- c*p + (1+d), p divides sum and first part => p divides second part
      exact (Nat.dvd_add_iff_right h1).mp hdvd
    have : 1 + d = p := by
      -- since 1+d <= p and p divides 1+d and 1+d > 0
      sorry
    omega
  have : padicValNat p (c * p + 1 + d) = 0 := padicValNat.eq_zero_of_not_dvd h_not_dvd
  rw [this]
  rfl
