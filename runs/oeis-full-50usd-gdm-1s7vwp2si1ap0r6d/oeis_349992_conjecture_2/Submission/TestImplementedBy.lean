import FormalConjectures.Util.ProblemImports

def my_func_impl (n : ℕ) : ℕ :=
  n + 10

@[implemented_by my_func_impl]
def my_func (n : ℕ) : ℕ :=
  1

theorem my_func_thm : my_func 5 = 1 := by
  rfl

#eval my_func 5
#print axioms my_func_thm
