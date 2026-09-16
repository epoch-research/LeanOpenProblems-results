import Submission.Spec
open Nat

def check_counter (n_max : ℕ) : IO Unit := do
  for n in [2:n_max] do
    for L in [1:15] do
      let mut is_run_0 := true
      for i in [0:L] do
        if a (n + i) != 0 then
          is_run_0 := false
          break
      if is_run_0 ∧ a (n + L) != 0 ∧ a (n - 1) != 0 then
        if L != 4 ∧ L != 5 then
          IO.println s!"Counterexample for 0: n={n}, L={L}"

      let mut is_run_1 := true
      for i in [0:L] do
        if a (n + i) != 1 then
          is_run_1 := false
          break
      if is_run_1 ∧ a (n + L) != 1 ∧ a (n - 1) != 1 then
        if L != 3 ∧ L != 4 then
          IO.println s!"Counterexample for 1: n={n}, L={L}"

#eval check_counter 50000
