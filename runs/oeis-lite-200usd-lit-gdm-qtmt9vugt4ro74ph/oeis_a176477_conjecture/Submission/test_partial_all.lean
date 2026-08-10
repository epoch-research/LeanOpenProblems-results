import FormalConjectures.Util.ProblemImports

def a_Q (n : ℕ) : ℚ := (n : ℚ)

partial def inst_all : ∀ n, Inhabited (PLift (∃ z, a_Q n = ↑z)) :=
  inst_all
