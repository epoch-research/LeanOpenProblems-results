import FormalConjectures.Util.ProblemImports
open scoped Nat.Prime

def a (n : ℕ) : ℕ :=
  Finset.card $ (Finset.Icc 1 n).filter fun k : ℕ =>
    let m := π (π (k * n))
    m.sqrt ^ 2 = m

example (n : ℕ) (hn : n > 0) : a n > 0 := by
  have hEq : (n > 0) = (a n > 0) := by
    apply propext
    constructor
    · intro _; exact ?_
    · intro _; exact hn
  exact Eq.mp hEq hn
