import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def classical_k (n : ℕ) : ℕ :=
  if h : ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1) then
    Classical.choose h
  else
    0


