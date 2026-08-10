import FormalConjectures.Util.ProblemImports
example {P Q : ℤ → Prop} (hp : ∃ x, P x) (hq : ∃ x, Q x) : Classical.choose hp = Classical.choose hq := by
  congr!
