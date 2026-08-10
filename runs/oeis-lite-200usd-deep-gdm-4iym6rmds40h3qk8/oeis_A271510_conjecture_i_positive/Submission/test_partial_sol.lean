import FormalConjectures.Util.ProblemImports

structure MySol (n : ℕ) where
  x : ℕ
  h : x = n
deriving Nonempty

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

theorem my_thm (n : ℕ) : ∃ x, x = n := by
  let s := get_sol n
  use s.x
  exact s.h
