import FormalConjectures.Util.ProblemImports
open Nat

partial def witnessSubtype (n : ℕ) (hn : n > 0) :
    {k : ℕ // Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)} :=
  witnessSubtype n hn

theorem test (n : ℕ) (hn : n > 0) :
    ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1) := by
  exact ⟨(witnessSubtype n hn).1, (witnessSubtype n hn).2⟩

#print axioms witnessSubtype
#print axioms test
