import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

-- First just see if fixed symbolic top case can be simplified by existing tactics.
set_option maxHeartbeats 800000
example (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) : (p^3 : ℕ) ∣ a (p-1) := by
  -- try the obvious reductions/automation; expected to fail, but maybe exposes subgoals
  unfold a
  apply?
