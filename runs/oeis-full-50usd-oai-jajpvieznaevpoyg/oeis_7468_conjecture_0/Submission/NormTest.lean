import FormalConjectures.Util.ProblemImports
noncomputable def a (n : ℕ) : ℕ :=
  let start_idx : ℕ := (n * (n - 1)) / 2
  Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime (start_idx + i)
example : Nat.nth Nat.Prime 10 = 31 := by norm_num
example : a 5 = 101 := by norm_num [a]
example : a 38 = 207936 := by norm_num [a]
