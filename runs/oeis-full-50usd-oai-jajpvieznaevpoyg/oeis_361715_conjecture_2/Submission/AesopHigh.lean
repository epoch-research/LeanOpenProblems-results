import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 2000000
open Nat Finset

def a (n : ℕ) : ℕ := ∑ k ∈ range n, (n.choose k) ^ 2 * multichoose n k
example (p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 2 ≤ r) :
  (a (p ^ r) : ℤ) ≡ a (p ^ (r - 1)) [ZMOD (p ^ (3 * r + 3) : ℕ)] := by
  aesop (add simp [a, Int.ModEq, Nat.Prime])
