import Submission.Spec
import Mathlib

def test : IO Unit := do
  let S : Finset ℕ := {0, 11, 57, 198, 229, 232, 1168, 2624}
  for n in [500:3000] do
    let a := A274007 n
    if a == 0 then
      IO.println s!"Zero: {n}"
    if a == 1 ∧ n ∉ S then
      IO.println s!"One not in S: {n}"
    if a != 1 ∧ n ∈ S then
      IO.println s!"In S but not one: {n}, {a}"

#eval test
