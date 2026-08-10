import FormalConjectures.Util.ProblemImports

def MyProp : Prop := True

unsafe def my_unsafe_proof : MyProp := MyProp.intro

@[implemented_by my_unsafe_proof]
opaque my_proof : MyProp

theorem my_theorem : MyProp := my_proof

#print axioms my_theorem
