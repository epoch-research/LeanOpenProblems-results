import FormalConjectures.Util.ProblemImports
open scoped Nat.Prime
#eval (2.sqrt ^ 2 = 2)
example : ¬ (2.sqrt ^ 2 = 2) := by norm_num

def a (n : ℕ) : ℕ :=
  Finset.card $ (Finset.Icc 1 n).filter fun k : ℕ =>
    let m := π (π (k * n))
    m.sqrt ^ 2 = m
example (n : ℕ) (hn : n>0) : a n > 0 := by
  simp [a]
  try omega
