import FormalConjectures.Util.ProblemImports

unsafe def my_unsafe_impl : False := my_unsafe_impl

@[implemented_by my_unsafe_impl]
def my_false : False := sorry

