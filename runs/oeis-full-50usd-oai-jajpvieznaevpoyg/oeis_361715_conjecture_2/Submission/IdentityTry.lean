import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  ∑ k ∈ range n, (n.choose k) ^ 2 * multichoose n k

def B (n : ℕ) : ℕ :=
  ∑ k ∈ range (n+1), (n.choose k)^2 * (n+k).choose k

example (n : ℕ) (hn : 0 < n) :
    5 * a n = 3 * B n + B (n-1) - 5 * (2*n-1).choose n := by
  induction n with
  | zero => cases hn
  | succ n ih =>
    simp [a, B, Nat.multichoose_eq]
    sorry
