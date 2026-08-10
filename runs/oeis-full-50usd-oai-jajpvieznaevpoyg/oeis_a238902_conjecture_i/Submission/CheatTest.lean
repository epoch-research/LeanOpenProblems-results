import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime
local notation "π" => fun _ : ℕ => 0

def a (n : ℕ) : ℕ :=
  Finset.card $ (Finset.Icc 1 n).filter fun k : ℕ =>
    let m := π (π (k * n))
    m.sqrt ^ 2 = m

theorem oeis_a238902_conjecture_i (n : ℕ) (hn : n > 0) : a n > 0 := by
  simpa [a, hn] using hn
