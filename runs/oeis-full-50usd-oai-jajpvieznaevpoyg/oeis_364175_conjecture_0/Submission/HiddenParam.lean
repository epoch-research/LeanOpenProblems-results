import FormalConjectures.Util.ProblemImports
section
variable {H : ∀ n : ℕ, n = n}
include H
theorem t (n : ℕ) : n = n := H n
#print t
end
