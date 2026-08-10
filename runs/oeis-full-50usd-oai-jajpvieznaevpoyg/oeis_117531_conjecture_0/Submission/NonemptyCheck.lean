import FormalConjectures.Util.ProblemImports
#check (inferInstance : Nonempty True)
-- #check (inferInstance : Nonempty False)
#check (Classical.choice : Nonempty False → False)
#check (Classical.choice : (∃ x : ℕ, x = x) → ℕ)
