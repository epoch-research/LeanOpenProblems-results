import FormalConjectures.Util.ProblemImports

open Nat Set

noncomputable def A053000 (n : ℕ) : ℕ :=
  (sInf {p | Nat.Prime p ∧ p > n ^ 2}) - n ^ 2

theorem A053000_one : A053000 1 = 1 := by
  have h_prime_two : Nat.Prime 2 := Nat.prime_two
  have hS : {p | Nat.Prime p ∧ p > 1}.Nonempty := ⟨2, h_prime_two, by decide⟩
  have h_mem : sInf {p | Nat.Prime p ∧ p > 1} ∈ {p | Nat.Prime p ∧ p > 1} := Nat.sInf_mem hS
  have h_gt : sInf {p | Nat.Prime p ∧ p > 1} > 1 := h_mem.2
  have h_ge : sInf {p | Nat.Prime p ∧ p > 1} ≥ 2 := h_gt
  have h_le : sInf {p | Nat.Prime p ∧ p > 1} ≤ 2 := Nat.sInf_le (show 2 ∈ {p | Nat.Prime p ∧ p > 1} from ⟨h_prime_two, by decide⟩)
  have h_eq : sInf {p | Nat.Prime p ∧ p > 1} = 2 := by omega
  change sInf {p | Nat.Prime p ∧ p > 1} - 1 = 1
  rw [h_eq]




theorem A053000_twelve : A053000 12 = 5 := by
  have h_prime_149 : Nat.Prime 149 := by decide
  have hS : {p | Nat.Prime p ∧ p > 144}.Nonempty := ⟨149, h_prime_149, by decide⟩
  have h_mem : sInf {p | Nat.Prime p ∧ p > 144} ∈ {p | Nat.Prime p ∧ p > 144} := Nat.sInf_mem hS
  have h_gt : sInf {p | Nat.Prime p ∧ p > 144} > 144 := h_mem.2
  have h_le : sInf {p | Nat.Prime p ∧ p > 144} ≤ 149 := Nat.sInf_le (show 149 ∈ {p | Nat.Prime p ∧ p > 144} from ⟨h_prime_149, by decide⟩)
  have h_not_prime : ∀ m, 144 < m ∧ m < 149 → ¬ Nat.Prime m := by
    intro m hm
    rcases hm with ⟨h1, h2⟩
    interval_cases m
    · intro h; revert h; decide
    · intro h; revert h; decide
    · intro h; revert h; decide
    · intro h; revert h; decide
  have h_eq : sInf {p | Nat.Prime p ∧ p > 144} = 149 := by
    by_contra h_neq
    have h_lt : sInf {p | Nat.Prime p ∧ p > 144} < 149 := lt_of_le_of_ne h_le h_neq
    exact h_not_prime (sInf {p | Nat.Prime p ∧ p > 144}) ⟨h_gt, h_lt⟩ h_mem.1
  change sInf {p | Nat.Prime p ∧ p > 144} - 144 = 5
  rw [h_eq]


