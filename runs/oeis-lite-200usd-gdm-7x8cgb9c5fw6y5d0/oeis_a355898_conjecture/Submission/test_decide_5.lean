import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000

open Nat

def A355898 : ℕ → ℕ
| 0 => 0
| 1 => 1
| 2 => 1
| n + 3 =>
  let an_minus_1 := A355898 (n + 2)
  let an_minus_2 := A355898 (n + 1)
  let g := Nat.gcd an_minus_1 an_minus_2
  g + (an_minus_1 + an_minus_2) / g

theorem base_conjecture_3775 :
  (A355898 3775 = 1 + A355898 3774 + A355898 3773)
  ∧ (A355898 3775 = 2 * A355898 3774 - A355898 3772)
  ∧ (A355898 3775 = (A355898 3774 + 1) * Nat.fib 3 - (A355898 3772 + 1) * Nat.fib 1 - 1) := by
  decide

theorem base_conjecture_3776 :
  (A355898 3776 = 1 + A355898 3775 + A355898 3774)
  ∧ (A355898 3776 = 2 * A355898 3775 - A355898 3773)
  ∧ (A355898 3776 = (A355898 3774 + 1) * Nat.fib 4 - (A355898 3772 + 1) * Nat.fib 2 - 1) := by
  decide
