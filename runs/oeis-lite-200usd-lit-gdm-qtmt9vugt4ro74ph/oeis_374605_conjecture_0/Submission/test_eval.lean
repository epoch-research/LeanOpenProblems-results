import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

theorem test_decide : (107^3 : ℕ) ∣ a 106 := by
  decide
