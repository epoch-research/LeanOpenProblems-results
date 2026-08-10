import Mathlib

set_option maxRecDepth 200000
set_option maxHeartbeats 0

open Nat

def witness (n : ℕ) : ℕ :=
  match n with
  | 300 => 1813
  | 301 => 3614
  | 302 => 2415
  | 303 => 1456
  | 304 => 3809
  | 305 => 1386
  | 306 => 8587
  | 307 => 980
  | 308 => 645
  | 309 => 1510
  | _ => 1

lemma witness_pos_and_mod_300 (n : ℕ) (h1 : 300 ≤ n) (h2 : n < 310) : witness n > 0 ∧ (witness n - 1) % Nat.totient (witness n) = n := by
  interval_cases n <;> decide
