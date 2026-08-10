import FormalConjectures.Util.ProblemImports

structure MyStruct where
  val : Prop

def my_struct_val : MyStruct := ⟨answer(sorry)⟩

#print axioms my_struct_val
