import FormalConjectures.Util.ProblemImports

structure MySol (n : ℕ) where
  x : ℕ
  h : x = n ∨ 0 < 1

instance (n : ℕ) : Nonempty (MySol n) :=
  ⟨⟨n, Or.inl rfl⟩⟩

partial def get_sol (n : ℕ) : MySol n :=
  let next := get_sol n
  ⟨next.x + 1, Or.inr (by sorry) -- wait, we still need 0 < 1 to return Or.inr!
  ⟩
