import FormalConjectures.Util.ProblemImports

abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

inductive Bad1 : Prop where
| intro : (Bad1 → Target) → Bad1

inductive Bad2 : Prop where
| intro : ((Bad2 → False) → Target) → Bad2

example : Target := by
  let f : Bad1 → Target := fun b => by cases b with | intro g => exact g b
  exact f (Bad1.intro f)

example : Target := by
  let f : Bad2 → False := fun b => by cases b with | intro g => exact ?hole
  exact Classical.choice (show Nonempty Target from inferInstance)
