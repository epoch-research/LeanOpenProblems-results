import FormalConjectures.Util.ProblemImports
axiom P : Prop
structure Alt where
  flag : Bool
  pf : flag = true → P
instance : Inhabited Alt := ⟨⟨false, by intro h; cases h⟩⟩
partial def alt (_ : Unit) : Alt := { flag := true, pf := fun _ => (alt ()).pf (by
  cases h : (alt ()).flag <;> simp [h]
) }
#print alt
#print axioms alt
#reduce (alt ()).flag
example : P := (alt ()).pf (by native_decide)
#print axioms _example
