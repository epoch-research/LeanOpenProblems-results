import FormalConjectures.Util.ProblemImports
#check inferInstanceAs (Nonempty (∀ n : ℕ, False → False))
#check inferInstanceAs (Nonempty (∀ P : Prop, P → P))
#check inferInstanceAs (Nonempty (∀ P : Prop, False → P))
#check inferInstanceAs (Nonempty (∀ P : Prop, True → P))
