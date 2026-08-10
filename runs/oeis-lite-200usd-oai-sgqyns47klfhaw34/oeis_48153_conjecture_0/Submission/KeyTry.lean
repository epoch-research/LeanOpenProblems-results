import FormalConjectures.Util.ProblemImports
open Finset

example (a b : ℕ) :
    (∑ t ∈ Finset.range (a*b), ((t^2 / b) % a)) ≤ b * (a * (a - 1) / 2) := by
  induction a generalizing b with
  | zero => simp
  | succ a ih =>
    -- try automation
    grind
