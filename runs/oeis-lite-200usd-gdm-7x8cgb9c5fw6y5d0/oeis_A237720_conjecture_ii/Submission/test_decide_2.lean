import FormalConjectures.Util.ProblemImports

open Nat

set_option allowUnsafeReducibility true
attribute [local reducible] Nat.sqrt
attribute [local reducible] Nat.sqrt.iter

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

lemma test_decide_2 : ∀ n < 1000, 2 < n → ∃ p < n, p.Prime ∧ (sqrt (n + p)).Prime := by
  decide
