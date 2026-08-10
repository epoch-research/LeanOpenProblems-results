import FormalConjectures.Util.ProblemImports

partial def badGoal (n : ℕ) (hn : n > 0) :
    ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1) :=
  badGoal n hn

#check badGoal
#print axioms badGoal
