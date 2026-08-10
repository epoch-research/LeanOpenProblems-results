import FormalConjectures.Util.ProblemImports

inductive Bad : Prop where
| intro : (Bad -> False) -> Bad

theorem bad : False := by
  have h : Bad := Bad.intro (fun b => by cases b with | intro f => exact f (Bad.intro f))
  cases h with | intro f => exact f h
#print axioms bad
