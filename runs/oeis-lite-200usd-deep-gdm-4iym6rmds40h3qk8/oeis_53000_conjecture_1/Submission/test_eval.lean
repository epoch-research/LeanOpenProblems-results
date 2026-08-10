import FormalConjectures.Util.ProblemImports
open Nat Set Classical

noncomputable def A053000 (n : ℕ) : ℕ :=
  (sInf {p | Nat.Prime p ∧ p > n ^ 2}) - n ^ 2

theorem test_4 : A053000 4 = 1 := by
  dsimp [A053000, sInf, InfSet.sInf]
  split_ifs with h
  · have h_mem : 17 ∈ {p | Nat.Prime p ∧ p > 4 ^ 2} := by
      refine ⟨by decide, by norm_num⟩
    have h_le := @Nat.find_le _ _ (fun a => propDecidable (Nat.Prime a ∧ a > 4 ^ 2)) h h_mem
    have h_smallest : ∀ x < 17, ¬(Nat.Prime x ∧ x > 4 ^ 2) := by
      intro x hx ⟨hp, hg⟩
      omega
    generalize h_find : @Nat.find (fun a => Nat.Prime a ∧ a > 4 ^ 2) (fun a => propDecidable (Nat.Prime a ∧ a > 4 ^ 2)) h = f
    rw [h_find] at h_le
    have h_eq : f = 17 := by
      have h_lt : 17 < f + 1 := by
        by_contra hc
        push_neg at hc
        -- hc : f < 17
        have h_spec := @Nat.find_spec (fun a => Nat.Prime a ∧ a > 4 ^ 2) (fun a => propDecidable (Nat.Prime a ∧ a > 4 ^ 2)) h
        rw [h_find] at h_spec
        exact h_smallest f hc h_spec
      omega
    rw [h_eq]
  · exfalso
    have h_mem : 17 ∈ {p | Nat.Prime p ∧ p > 4 ^ 2} := ⟨by decide, by norm_num⟩
    exact h ⟨17, h_mem⟩
