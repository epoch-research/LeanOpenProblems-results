import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

def A282459 (n : ℕ) : ℕ :=
  let upper_k : ℕ := log 2 (2 * n + 1)
  let s := Finset.Icc 1 upper_k
  let is_composite (m : ℕ) : Prop := 1 < m ∧ ¬ Nat.Prime m
  let seq_val (k : ℕ) : ℕ := 2 * n + 1 - 2 ^ k
  Finset.card (Finset.filter (fun k : ℕ => is_composite (seq_val k)) s)

theorem test_small : ∀ n ∈ Finset.Ico 53 500, A282459 n > 0 := by
  decide
