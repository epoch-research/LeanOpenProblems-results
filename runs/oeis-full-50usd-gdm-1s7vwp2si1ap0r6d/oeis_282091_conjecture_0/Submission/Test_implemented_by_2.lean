import FormalConjectures.Util.ProblemImports

def MyProp : Prop := True

instance : Inhabited MyProp := ⟨True.intro⟩

unsafe def my_unsafe_proof : MyProp := True.intro

@[implemented_by my_unsafe_proof]
opaque my_proof : MyProp

theorem my_theorem : MyProp := my_proof

#print axioms my_theorem
