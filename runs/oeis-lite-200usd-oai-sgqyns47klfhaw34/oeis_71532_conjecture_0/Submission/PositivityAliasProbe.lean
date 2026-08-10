import FormalConjectures.Util.ProblemImports

abbrev Neg (α : Type) := α → False
-- should be rejected
inductive Bad1 : Type where
| intro : Neg Bad1 → Bad1

structure Contra (α : Type) where
  run : α → False

inductive Bad2 : Type where
| intro : Contra Bad2 → Bad2

example : False := by
  let f : Bad2 → False := fun b => match b with | Bad2.intro c => c.run b
  exact f (Bad2.intro ⟨f⟩)
