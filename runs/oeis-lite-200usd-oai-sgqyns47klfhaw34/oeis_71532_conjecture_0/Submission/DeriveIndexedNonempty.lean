import FormalConjectures.Util.ProblemImports
axiom P : Prop

inductive T : Bool → Type where
| mk : T false

deriving instance Nonempty for T
#check (inferInstance : Nonempty (T false))
#check (inferInstance : Nonempty (T true))
example : P := by cases (Classical.choice (inferInstance : Nonempty (T true)))

inductive W : Prop → Type where
| mk : W True

deriving instance Nonempty for W
#check (inferInstance : Nonempty (W False))
example : P := by cases (Classical.choice (inferInstance : Nonempty (W False)))
