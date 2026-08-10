import FormalConjectures.Util.ProblemImports

inductive Curry : Prop where
| intro : (Curry → False) → Curry

-- If accepted, derive contradiction
example : False := by
  let c : Curry := Curry.intro (fun h => by cases h with | intro f => exact f h)
  cases c with | intro f => exact f c
