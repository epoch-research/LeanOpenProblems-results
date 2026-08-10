import FormalConjectures.Util.ProblemImports
open scoped Nat.Prime

def a (n : ℕ) : ℕ :=
  Finset.card $ (Finset.Icc 1 n).filter fun k : ℕ =>
    let m := π (π (k * n))
    m.sqrt ^ 2 = m

theorem dis : ¬ ((n : ℕ) → n > 0 → a n > 0) := by
  intro h
  let rec p : 0 > 0 := h 0 p
  exact Nat.lt_irrefl 0 p
#print axioms dis
