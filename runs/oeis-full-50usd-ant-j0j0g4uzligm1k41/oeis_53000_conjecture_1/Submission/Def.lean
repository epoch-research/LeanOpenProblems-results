import FormalConjectures.Util.ProblemImports
open Nat Set

noncomputable def A053000 (n : ℕ) : ℕ :=
  (sInf {p | Nat.Prime p ∧ p > n ^ 2}) - n ^ 2

-- Prove sInf {p | p.Prime ∧ p > 144} = 149 directly.
example : sInf {p | Nat.Prime p ∧ p > 12 ^ 2} = 149 := by
  have h : {p | Nat.Prime p ∧ p > 12 ^ 2} = {p | Nat.Prime p ∧ p > 144} := by norm_num
  apply le_antisymm
  · apply Nat.sInf_le
    constructor
    · norm_num
    · norm_num
  · apply le_csInf
    · exact ⟨149, by norm_num, by norm_num⟩
    · intro b hb
      obtain ⟨hp, hgt⟩ := hb
      by_contra hlt
      push_neg at hlt
      interval_cases b <;> simp_all (config := {decide := true}) <;> omega
