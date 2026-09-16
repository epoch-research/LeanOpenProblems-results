import FormalConjectures.Util.ProblemImports

theorem my_test : ∀ n : ℕ, n = n := fun n => rfl

#check type_of% my_test
