import FormalConjectures.Util.ProblemImports

abbrev Q := Quot (fun _ _ : Prop => True)
def q (P : Prop) : Q := Quot.mk _ P

inductive Bad : Q -> Type where
| good : Bad (q True)
| bad : False -> Bad (q False)

example : Bad (q False) := by
  have h : q True = q False := (Quot.sound trivial)
  exact Eq.mp (congrArg Bad h) Bad.good

example : False := by
  have h : q True = q False := (Quot.sound trivial)
  let x : Bad (q False) := Eq.mp (congrArg Bad h) Bad.good
  -- try cases/noConfusion
  cases x with
  | good => exact False.elim (by contradiction)
  | bad f => exact f

#print axioms QuotIndexedNoConfusion._example_1
#print axioms QuotIndexedNoConfusion._example_2
