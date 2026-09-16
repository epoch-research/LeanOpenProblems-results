import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma zify_magic (p : ℕ) (hp5 : 5 ≤ p) :
  let c := (p - 1) * (p - 3) / 2
  let M := c * p + 1
  let n := p * p - 2 * p
  2 * M = (p - 2) * (n - 1) := by
  intro c M n
  have H0 : 2 * c = (p - 1) * (p - 3) := by
    apply Nat.mul_div_cancel'
    -- (p-1) is even because p is odd
    sorry
  have H1 : (2 * M : ℤ) = ((p - 2) * (n - 1) : ℤ) := by
    push_cast
    -- substitute c
    sorry
