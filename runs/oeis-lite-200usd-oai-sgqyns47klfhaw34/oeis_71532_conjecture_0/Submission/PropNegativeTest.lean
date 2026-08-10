import FormalConjectures.Util.ProblemImports

inductive BadProp : Prop where
| intro : (BadProp -> False) -> BadProp

structure BadStruct : Prop where
  f : BadStruct -> False

example : False := by
  let b : BadProp := .intro (fun h => by cases h with | intro f => exact f h)
  cases b with | intro f => exact f b
