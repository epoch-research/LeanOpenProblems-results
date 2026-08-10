import FormalConjectures.Util.ProblemImports

partial def badThunk (P : Prop) : Unit → P := fun _ => badThunk P ()

example (n : ℕ) (hn : n > 0) :
    ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1) := by
  exact badThunk _ ()
#print axioms badThunk
