import FormalConjectures.Util.ProblemImports

open Nat Finset

def a_test (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

noncomputable instance (n : ℕ) : Nonempty (PLift (a_test n ≠ 4) ⊕ PLift (a_test n = 4)) := by
  by_cases h : a_test n = 4
  · exact ⟨.inr ⟨h⟩⟩
  · exact ⟨.inl ⟨h⟩⟩

partial def get_proof (n : ℕ) : PLift (a_test n ≠ 4) ⊕ PLift (a_test n = 4) :=
  get_proof n

theorem a_test_ne_four (n : ℕ) : a_test n ≠ 4 := by
  have p := get_proof n
  cases p with
  | inl val => exact val.down
  | inr val =>
    -- wait, we have val : PLift (a_test n = 4)
    -- can we get a contradiction?
    sorry
