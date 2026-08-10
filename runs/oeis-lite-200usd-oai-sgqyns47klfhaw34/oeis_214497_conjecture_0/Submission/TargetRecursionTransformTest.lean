import FormalConjectures.Util.ProblemImports
open Nat

-- If a witness for n has even j, it gives a witness for n+1 by halving j.
lemma lift_if_even {n j : ℕ} (hj : Even j)
    (h : Nat.Prime (j * (2 ^ n) - 1) ∧ Nat.Prime (j * (2 ^ n) + 1)) :
    ∃ j' : ℕ, Nat.Prime (j' * (2 ^ (n+1)) - 1) ∧ Nat.Prime (j' * (2 ^ (n+1)) + 1) := by
  rcases hj with ⟨j', rfl⟩
  refine ⟨j', ?_⟩
  have hm : j' * 2 * 2 ^ n = j' * 2 ^ (n+1) := by ring_nf; rw [pow_succ]
  -- ring_nf on Nat not enough maybe
  sorry
