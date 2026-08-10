import FormalConjectures.Util.ProblemImports

unsafe def my_impl (n : ℕ) : n = n + 1 := my_impl n

@[implemented_by my_impl]
opaque test_thm (n : ℕ) : n = n + 1

#print axioms test_thm
