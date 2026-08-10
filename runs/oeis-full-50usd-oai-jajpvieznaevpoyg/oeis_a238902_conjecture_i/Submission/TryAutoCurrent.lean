import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime

def a (n : ℕ) : ℕ :=
  Finset.card $ (Finset.Icc 1 n).filter fun k : ℕ =>
    let m := π (π (k * n))
    m.sqrt ^ 2 = m

example (n : ℕ) (hn : n > 0) : a n > 0 := by
  unfold a
  -- try to expose goal
  change 0 < Finset.card ((Finset.Icc 1 n).filter fun k : ℕ => (π (π (k * n))).sqrt ^ 2 = π (π (k * n)))
  -- aesop?
  aesop
