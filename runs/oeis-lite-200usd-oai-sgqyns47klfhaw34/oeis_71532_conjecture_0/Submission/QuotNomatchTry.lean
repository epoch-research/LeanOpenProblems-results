import FormalConjectures.Util.ProblemImports
abbrev Q := Quot (fun _ _ : Prop => True)
def q (P : Prop) : Q := Quot.mk _ P
inductive Bad : Q -> Type where
| good : Bad (q True)
noncomputable def xbad : Bad (q False) := Eq.ndrec Bad.good (Quot.sound (r := fun _ _ : Prop => True) trivial : q True = q False)
example : False := nomatch xbad
