import Submission.Spec
import Mathlib

def check_all : IO Unit := do
  let S : Finset ℕ := {0, 11, 57, 198, 229, 232, 1168, 2624}
  for n in [300:1000] do
    let a := A274007 n
    if a == 0 then
      IO.println s!"Zero at {n}"
    let b := a == 1
    let c := if n ∈ S then true else false
    if b != c then
      IO.println s!"Counterexample at {n}: a={a}, expected={c}"

#eval check_all
