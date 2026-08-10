import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.GCD.Basic

open Nat

def x_seq : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 1 => 2 * (x_seq n) + Nat.lcm (x_seq n) (n + 1)

set_option maxRecDepth 20000000

lemma q_dvd_x_seq_q_sq_all_small : ∀ q, q ≤ 360 → Nat.Prime q → q ∣ x_seq (q * q - 1) := by
  decide
