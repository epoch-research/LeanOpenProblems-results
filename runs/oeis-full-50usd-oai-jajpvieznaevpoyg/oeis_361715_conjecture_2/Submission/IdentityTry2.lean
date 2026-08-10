import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  ∑ k ∈ range n, (n.choose k) ^ 2 * multichoose n k

def B (n : ℕ) : ℕ :=
  ∑ k ∈ range (n+1), (n.choose k)^2 * (n+k).choose k

example (n : ℕ) : (∑ k ∈ range (n+1), (n.choose k)^2 * (n+k-1).choose k)
    = (3 * B n + B (n-1)) / 5 := by
  induction n with
  | zero => native_decide
  | succ n ih =>
    simp [B, Nat.choose_succ_succ, Nat.multichoose_eq] at *
    sorry
