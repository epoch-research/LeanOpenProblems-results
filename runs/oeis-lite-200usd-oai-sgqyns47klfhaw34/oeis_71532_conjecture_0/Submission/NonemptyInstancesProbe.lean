import FormalConjectures.Util.ProblemImports

#check inferInstanceAs (Nonempty ((P : Prop) → P))
#check inferInstanceAs (Inhabited ((P : Prop) → P))
#check inferInstanceAs (Nonempty (∀ P : Prop, Decidable P))
#check inferInstanceAs (Inhabited (∀ P : Prop, Decidable P))
#check inferInstanceAs (Nonempty (∀ P : Prop, Nonempty P))
#check inferInstanceAs (Nonempty (∀ P : Prop, ¬ P))
#check inferInstanceAs (Nonempty (Erased False))
#check inferInstanceAs (Inhabited (Erased False))
#check inferInstanceAs (Nonempty (Trunc False))
#check inferInstanceAs (Inhabited (Trunc False))
#check inferInstanceAs (Nonempty (Plausible.TestResult False))
#check inferInstanceAs (Inhabited (Plausible.TestResult False))
