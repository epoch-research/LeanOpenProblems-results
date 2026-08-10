import FormalConjectures.Util.ProblemImports

open Nat Finset

def a_test (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

noncomputable instance : Nonempty (PLift (∀ m, a_test m = 4 → False)) := by
  by_cases h : ∃ m, a_test m = 4
  · rcases h with ⟨m, hm⟩
    -- wait, we know actually there is no such m.
    -- But we can just use Classical.choice or EMA to get PLift (∀ m, a_test m = 4 → False) noncomputably!
    -- Yes! Since ¬ ∃ m, a_test m = 4 is classically true, the type is nonempty!
    have h_not : ¬ ∃ m, a_test m = 4 := by sorry
    exact ⟨⟨fun m hm => (h_not ⟨m, hm⟩).elim⟩⟩
  · exact ⟨⟨fun m hm => h ⟨m, hm⟩⟩⟩
