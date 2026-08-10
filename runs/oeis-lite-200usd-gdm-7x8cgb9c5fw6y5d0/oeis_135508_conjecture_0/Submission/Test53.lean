import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 100000

open Nat

def x_seq : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 1 => 2 * (x_seq n) + Nat.lcm (x_seq n) (n + 1)

lemma dvd_179_aux : 227 ∣ x_seq 6581 := by decide
