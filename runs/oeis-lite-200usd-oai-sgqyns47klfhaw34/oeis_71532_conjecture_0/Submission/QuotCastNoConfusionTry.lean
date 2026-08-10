import FormalConjectures.Util.ProblemImports

abbrev Q := Quot (fun _ _ : Prop => True)
def q (P : Prop) : Q := Quot.mk _ P

inductive Bad : Q -> Type where
| good : Bad (q True)
| bad : False -> Bad (q False)

#check Bad.noConfusion
#check Bad.noConfusionType

noncomputable def xbad : Bad (q False) := by
  exact Eq.ndrec Bad.good (Quot.sound (r := fun _ _ : Prop => True) trivial : q True = q False)

#check xbad
#print xbad
#print axioms xbad

-- Try noConfusion with a hypothetical equality to bad constructor impossible?
example : False := by
  let x := xbad
  -- maybe cases blocked
  -- exact Bad.noConfusion ?
  cases x with
  | good => contradiction
  | bad f => exact f

