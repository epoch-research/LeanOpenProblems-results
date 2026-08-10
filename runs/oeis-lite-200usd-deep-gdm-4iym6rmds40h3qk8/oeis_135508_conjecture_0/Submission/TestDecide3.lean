import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.GCD.Basic

open Nat

def x_seq_loop : ℕ → ℕ → ℕ → ℕ
| 0, _, x => x
| n + 1, i, x => x_seq_loop n (i + 1) (2 * x + Nat.lcm x i)

def x_seq_tr (n : ℕ) : ℕ :=
  if n = 0 then 0
  else x_seq_loop (n - 1) 2 1

set_option maxRecDepth 20000000

lemma q_dvd_x_seq_q_sq_all_small_tr : ∀ q, q ≤ 360 → Nat.Prime q → q ∣ x_seq_tr (q * q - 1) := by
  decide
