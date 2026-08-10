import FormalConjectures.Util.ProblemImports

partial def f (k : ℕ) : ℕ :=
  if k = 0 then 0 else f (k - 1) + 1

theorem f_zero : f 0 = 0 := by
  rfl
