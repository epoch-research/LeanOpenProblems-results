import FormalConjectures.Util.ProblemImports
open Nat

-- A proof-free computable predicate using Decidable Nat.Prime. For symbolic n/k this is opaque to reduction.
def good (n k : ℕ) : Prop := Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

noncomputable def decGood (n k : ℕ) : Decidable (good n k) := Classical.dec _

partial def searchFrom (n k : ℕ) : ℕ :=
  if h : good n k then k else searchFrom n (k+1)

example (n : ℕ) (hn : n > 0) : ∃ k, good n k := by
  let k := searchFrom n 0
  use k
  unfold k
  unfold searchFrom
  -- see if unfolding produces if with proof branch
  dsimp [decGood, good]
  sorry
