import FormalConjectures.Util.ProblemImports
example (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) : False := by
  aesop
