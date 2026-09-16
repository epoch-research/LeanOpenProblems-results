import Mathlib

def empty_loop (d fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => d
  | f + 1 => empty_loop (d + 1) f

def run_many (len fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | f + 1 =>
    if len == 0 then 0
    else if len == 1 then empty_loop 0 2500
    else
      let half := len / 2
      run_many half f + run_many (len - half) f

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem t : run_many 10000 20000 = 25000000 := by decide
