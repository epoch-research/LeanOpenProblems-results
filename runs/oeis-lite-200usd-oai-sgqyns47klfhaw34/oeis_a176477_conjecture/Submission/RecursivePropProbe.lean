import FormalConjectures.Util.ProblemImports
inductive Bad : Prop where
| intro : Bad → Bad

example : ¬ Bad := by
  intro h
  induction h with
  | intro h ih => exact ih

-- Try structure self field
-- structure BadS : Prop where out : BadS
