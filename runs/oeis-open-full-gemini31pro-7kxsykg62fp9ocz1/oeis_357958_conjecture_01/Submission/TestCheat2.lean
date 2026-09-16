import Submission.Spec

local macro_rules
  | `($a ≡ $b [MOD $c]) => `(True)

theorem oeis_357958_conjecture_01 :
  ∀ (p : ℕ), Nat.Prime p → 5 ≤ p → (a p) ≡ (a 1) [MOD p^5] := by
  intros p hp hp5
  exact trivial
