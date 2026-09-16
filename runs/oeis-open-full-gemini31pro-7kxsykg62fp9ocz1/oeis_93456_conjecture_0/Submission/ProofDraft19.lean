import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma M_eq (p : ℕ) (hp5 : 5 ≤ p) :
  let n := p * p - 2 * p
  let c := (p - 1) * (p - 3) / 2
  let M := c * p + 1
  2 * M = (p - 2) * (n - 1) := by
  intro n c M
  have H : (p - 1) * (p - 3) * p + 2 = (p - 2) * (p * p - 2 * p - 1) := by
    nlinarith
  sorry
