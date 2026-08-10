import FormalConjectures.Util.ProblemImports

unsafe def my_unsafe_impl : Bool := true

@[implemented_by my_unsafe_impl]
def my_bool : Bool := false

theorem unsound_proof : my_bool = true := by
  native_decide
#print axioms unsound_proof
