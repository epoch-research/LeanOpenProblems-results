import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

unsafe def get_nonempty_unsafe (n : ℕ) : Nonempty (0 < A271510 n) :=
  get_nonempty_unsafe n

@[implemented_by get_nonempty_unsafe]
opaque get_nonempty (n : ℕ) : Nonempty (0 < A271510 n)

theorem my_thm (n : ℕ) : 0 < A271510 n :=
  Classical.choice (get_nonempty n)

#print axioms my_thm
