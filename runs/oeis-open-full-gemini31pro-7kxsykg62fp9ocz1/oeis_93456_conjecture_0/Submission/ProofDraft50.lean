import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ :=
  let L := n.choose 2 + 1
  let R := (n + 1).choose 2
  let is_composite (k : ℕ) : Prop := 1 < k ∧ ¬ k.Prime
  (Icc L R).filter is_composite |>.prod id

theorem oeis_93456_conjecture_0.disproof : ¬ (Set.Finite {n : ℕ | n > 1 ∧ ¬ (a (n - 1) ∣ a n)}) := by
  sorry
