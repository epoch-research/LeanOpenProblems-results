import FormalConjectures.Util.ProblemImports
axiom P : Prop
structure Alt where
  flag : Bool
  pf : flag = true → P

deriving instance Inhabited for Alt
partial def alt : Alt := { flag := true, pf := fun _ => (alt).pf rfl }
#print alt
#print axioms alt
#reduce alt.flag
example : alt.flag = true := by native_decide
example : P := alt.pf (by native_decide)
#print axioms _example
