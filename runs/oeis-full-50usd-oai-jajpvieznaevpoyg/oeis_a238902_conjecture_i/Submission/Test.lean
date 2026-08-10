import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime

def aa (n : ℕ) : ℕ :=
  Finset.card $ (Finset.Icc 1 n).filter fun k : ℕ =>
    let m := π (π (k * n))
    m.sqrt ^ 2 = m

example (n : ℕ) (hn : n > 0) : aa n > 0 := by
  native_decide +revert
