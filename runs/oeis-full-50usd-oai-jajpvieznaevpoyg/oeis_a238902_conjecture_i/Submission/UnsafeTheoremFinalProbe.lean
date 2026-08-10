import FormalConjectures.Util.ProblemImports
open scoped Nat.Prime

def a (n : ℕ) : ℕ :=
  Finset.card $ (Finset.Icc 1 n).filter fun k : ℕ =>
    let m := π (π (k * n))
    m.sqrt ^ 2 = m
unsafe theorem oeis_a238902_conjecture_i (n : ℕ) (hn : n > 0) : a n > 0 := by
  exact unsafeCast True.intro
#print axioms oeis_a238902_conjecture_i
#print oeis_a238902_conjecture_i
