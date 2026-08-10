import FormalConjectures.Util.ProblemImports
open Finset Nat
noncomputable def a (n : ℕ) : ℕ :=
  let pn : ℕ := Nat.nth Nat.Prime (n - 1)
  Finset.card (Finset.filter (fun k : ℕ => Nat.Prime (k ^ 2 - k + pn)) (Finset.Icc 1 n))

theorem tu : ∀ n : ℕ, n > 13 → a n < n := by
  decide

#print axioms tu
