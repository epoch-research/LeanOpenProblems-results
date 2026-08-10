import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 10000000

open Nat

lemma minfac_le_103_part1 : ∀ p, p < 2000 → ¬ Nat.Prime (p - 2) → Nat.minFac (p - 2) ≤ 103 := by
  decide

lemma minfac_le_103_part2 : ∀ p, 2000 ≤ p ∧ p < 4000 → ¬ Nat.Prime (p - 2) → Nat.minFac (p - 2) ≤ 103 := by
  decide
