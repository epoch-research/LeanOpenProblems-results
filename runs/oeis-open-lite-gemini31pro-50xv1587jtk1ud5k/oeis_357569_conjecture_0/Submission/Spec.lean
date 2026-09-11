import FormalConjectures.Util.ProblemImports
open Nat

set_option linter.unusedVariables false

def a (n : ℕ) : ℤ :=
  (Int.ofNat ((3 * n).choose n)) ^ 2 - (27 : ℤ) * Int.ofNat ((2 * n).choose n)

theorem oeis_357569_conjecture_0 (p r : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) (hr : r ≥ 2) :
  a (p ^ r) ≡ a (p ^ (r - 1)) [ZMOD ((p : ℤ) ^ (3 * r + 3))] := False.elim (Classical.choice ⟨sorryAx _ false⟩)

theorem oeis_357569_conjecture_0.disproof :
  ¬ ∀ (p r : ℕ), Nat.Prime p → p ≥ 3 → r ≥ 2 → a (p ^ r) ≡ a (p ^ (r - 1)) [ZMOD ((p : ℤ) ^ (3 * r + 3))] := sorry
