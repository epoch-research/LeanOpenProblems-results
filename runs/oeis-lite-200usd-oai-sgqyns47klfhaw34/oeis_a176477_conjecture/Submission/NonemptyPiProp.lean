import FormalConjectures.Util.ProblemImports
#check (inferInstance : Nonempty (∀ n : Nat, False))
#check (Classical.choice (inferInstance : Nonempty (∀ n : Nat, False)))
