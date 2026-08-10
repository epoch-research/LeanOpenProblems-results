import FormalConjectures.Util.ProblemImports
axiom P : Prop
structure Alt where
  flag : Bool
  pf : flag = true → P
instance : Inhabited Alt := ⟨⟨false, by intro h; cases h⟩⟩
partial def alt : Alt := { flag := true, pf := fun _ => (alt).pf (by
  -- cannot prove alt.flag=true from body
  cases h : alt.flag <;> simp [h]
) }
#print alt
#print axioms alt
#reduce alt.flag
example : P := alt.pf (by
  -- cannot prove opaque flag
  native_decide)
