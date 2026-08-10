import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime

def a (n : ℕ) : ℕ :=
  Finset.card $ (Finset.Icc 1 n).filter fun k : ℕ =>
    let m := π (π (k * n))
    m.sqrt ^ 2 = m

theorem exa1 : a 1 > 0 := by
  decide

#print axioms exa1

theorem expi100 : π 100 = 25 := by
  decide

#print axioms expi100

#print axioms a
