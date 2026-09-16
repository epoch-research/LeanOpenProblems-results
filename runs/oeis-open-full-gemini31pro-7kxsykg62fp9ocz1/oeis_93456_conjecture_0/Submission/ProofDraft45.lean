import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma padicValNat_le_one (p c d : ℕ) [Fact p.Prime] (h1 : 1 ≤ d) (h2 : d < p) :
  padicValNat p (p * (c * p + 1 + d)) = 1 := by
  have hp : p.Prime := Fact.out
  have hp1 : 1 < p := hp.one_lt
  have h_ne : c * p + 1 + d ≠ 0 := by omega
  rw [padicValNat.mul hp.ne_zero h_ne]
  have : padicValNat p p = 1 := padicValNat.self hp1
  rw [this]
  have h_not_dvd : ¬ (p ∣ c * p + 1 + d) := by
    intro hdvd
    have h1_dvd : p ∣ c * p := dvd_mul_left p c
    have hdvd_add : p ∣ (c * p) + (1 + d) := by
      have : c * p + 1 + d = (c * p) + (1 + d) := by omega
      rw [← this]
      exact hdvd
    have h2_dvd : p ∣ 1 + d := (Nat.dvd_add_iff_right h1_dvd).mp hdvd_add
    have : 1 + d = p := by
      apply le_antisymm
      · omega
      · exact Nat.le_of_dvd (by omega) h2_dvd
    omega
  have : padicValNat p (c * p + 1 + d) = 0 := padicValNat.eq_zero_of_not_dvd h_not_dvd
  rw [this]
