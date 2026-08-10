import FormalConjectures.Util.ProblemImports

partial def badSub (n : ℕ) (hn : n > 0) :
    {k : ℕ // Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)} :=
  badSub n hn

example (n : ℕ) (hn : n > 0) :
    ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1) := by
  exact ⟨(badSub n hn).1, (badSub n hn).2⟩
#print axioms badSub
