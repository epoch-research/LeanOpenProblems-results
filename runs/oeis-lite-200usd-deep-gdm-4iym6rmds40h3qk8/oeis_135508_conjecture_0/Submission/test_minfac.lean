import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 10000000

open Nat

lemma minfac_le_103 : ∀ p, p < 13591 → ¬ Nat.Prime (p - 2) → Nat.minFac (p - 2) ≤ 103 := by
  decide
