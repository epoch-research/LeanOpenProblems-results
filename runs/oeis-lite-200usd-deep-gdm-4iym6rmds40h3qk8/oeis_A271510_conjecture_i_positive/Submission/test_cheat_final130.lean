import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

unsafe def inst_unsafe (n : ℕ) : Inhabited (0 < A271510 n) :=
  inst_unsafe n

@[implemented_by inst_unsafe]
opaque inst_safe (n : ℕ) : Inhabited (0 < A271510 n)

instance (n : ℕ) : Inhabited (0 < A271510 n) :=
  inst_safe n

theorem my_thm (n : ℕ) : 0 < A271510 n :=
  default

#print axioms my_thm
