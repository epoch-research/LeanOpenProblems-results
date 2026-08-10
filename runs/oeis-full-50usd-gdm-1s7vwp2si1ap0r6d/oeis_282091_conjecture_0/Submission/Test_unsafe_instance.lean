import FormalConjectures.Util.ProblemImports

def MyProp : Prop := False

unsafe def my_unsafe_proof : MyProp :=
  my_unsafe_proof

unsafe instance : Inhabited MyProp := ⟨my_unsafe_proof⟩

@[implemented_by my_unsafe_proof]
opaque my_proof : MyProp

theorem my_theorem : MyProp := my_proof

#print axioms my_theorem
