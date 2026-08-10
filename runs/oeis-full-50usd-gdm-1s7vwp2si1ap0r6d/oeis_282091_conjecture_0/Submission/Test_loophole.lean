import FormalConjectures.Util.ProblemImports

def MyProp : Prop := False

unsafe def my_unsafe_proof : MyProp :=
  my_unsafe_proof

unsafe def unsafe_inhabited : Inhabited (Inhabited MyProp) :=
  ⟨⟨my_unsafe_proof⟩⟩

@[implemented_by unsafe_inhabited]
opaque instMyProp : Inhabited MyProp

theorem my_theorem : MyProp :=
  @Inhabited.default MyProp instMyProp

#print axioms my_theorem
