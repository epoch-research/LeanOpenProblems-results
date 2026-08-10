import FormalConjectures.Util.ProblemImports
partial def decLoop (P : Prop) : Decidable P := decLoop P

-- Can an opaque Decidable P be coerced to P? No; the false branch remains.
example (P : Prop) : Decidable P := decLoop P

example (P : Prop) : (if h : P then True else True) := by
  by_cases h : P <;> trivial

-- This is exactly the obstruction:
example (P : Prop) : (if h : P then P else True) := by
  by_cases h : P
  · exact h
  · trivial

-- But proving P from this still requires knowing the if chose the true branch.
example (P : Prop) : (if h : P then P else True) → P := by
  intro hif
  by_cases h : P
  · exact h
  · -- hif is just True here
    simp [h] at hif
    fail_if_success exact hif
    exact False.elim (h ?_)
