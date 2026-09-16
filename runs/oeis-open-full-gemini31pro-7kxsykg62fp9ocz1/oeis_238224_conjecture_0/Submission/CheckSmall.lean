import Submission.Spec
open Nat

def A238224_comp (n : ℕ) : ℕ :=
  Id.run <| do
    let mut sum := 0
    for j in [1:n] do
      let upper_q := (n - 1) / j
      for q in [1:upper_q+1] do
        let k := j * q + 1
        if Nat.primeCounting (k * n) % Nat.primeCounting (j * n) == 0 then
          sum := sum + 1
    return sum

def findCounterexample (maxN : ℕ) : IO Unit := do
  for n in [2:maxN] do
    if A238224_comp n == 0 then
      IO.println s!"Counterexample found: {n}"
  IO.println "Done."

#eval findCounterexample 100
