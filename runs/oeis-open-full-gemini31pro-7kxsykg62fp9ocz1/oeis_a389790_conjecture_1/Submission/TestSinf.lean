import FormalConjectures.Util.ProblemImports
open Classical

theorem sinf_empty : sInf (∅ : Set ℕ) = 0 := by
  exact Nat.sInf_empty

theorem sinf_nonempty (s : Set ℕ) (h : s.Nonempty) : sInf s ∈ s ∧ ∀ x ∈ s, sInf s ≤ x := by
  exact ⟨Nat.sInf_mem h, fun x hx => Nat.sInf_le hx⟩
