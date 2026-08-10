import FormalConjectures.Util.ProblemImports

theorem prop_girard : False := by
  let F (X : Prop) := (Set (Set X) → X) → Set (Set X)
  let U := ∀ X : Prop, F X
  let G (T : Set (Set U)) (X : Prop) : F X := fun f => {p | {x : U | f (x X f) ∈ p} ∈ T}
  let τ (T : Set (Set U)) : U := fun X => G T X
  let σ (S : U) : Set (Set S) := sorry
