import Mathlib

open Nat

lemma TPC_implication :
  Set.Finite {n : ℕ | (Finset.range (6 * n + 3)).filter (fun p => p.Prime ∧ (p - 2).Prime ∧ (6 * n - p).Prime ∧ (6 * n + 2 - p).Prime) = ∅} →
  ¬ Set.Finite {p : ℕ | p.Prime ∧ (p - 2).Prime} := by
  sorry
