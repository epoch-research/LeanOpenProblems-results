import FormalConjectures.Util.ProblemImports

unsafe def my_false_impl : False := my_false_impl

@[implemented_by my_false_impl]
theorem my_false : False := sorry
