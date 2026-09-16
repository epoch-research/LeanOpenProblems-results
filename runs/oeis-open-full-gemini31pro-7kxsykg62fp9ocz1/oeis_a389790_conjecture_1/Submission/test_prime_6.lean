import FormalConjectures.Util.ProblemImports
open Classical
open Nat

noncomputable def next_prime (r : ℕ) : ℕ :=
  sInf {k : ℕ | Nat.Prime k ∧ r < k}

lemma sInf_eq_find (S : Set ℕ) (h : ∃ x, x ∈ S) : sInf S = Nat.find h := by
  sorry
