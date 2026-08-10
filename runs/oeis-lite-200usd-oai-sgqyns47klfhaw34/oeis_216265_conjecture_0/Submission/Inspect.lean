import FormalConjectures.Util.ProblemImports

open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

example (n : ℕ) (h : n > 13) : A216265 n > 0 := by
  unfold A216265 Nat.primeCounting Nat.primeCounting'
  simp only [gt_iff_lt, tsub_pos_iff_lt]
  trace_state
  sorry
