import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 500000
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 4000000

open Nat

def x_seq_loop : ℕ → ℕ → ℕ → ℕ
  | 0, _, acc => acc
  | i + 1, idx, acc => x_seq_loop i (idx + 1) (2 * acc + Nat.lcm acc idx)

def x_seq_tail (n : ℕ) : ℕ :=
  if n = 0 then 0 else x_seq_loop (n - 1) 2 1

lemma dvd_1031_test : 1031 ∣ x_seq_tail 5153 := by
  decide
