import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime
local notation:1024 "π" => (fun _ : ℕ => 0)
#check π 3

def a (n : ℕ) : ℕ :=
  Finset.card $ (Finset.Icc 1 n).filter fun k : ℕ =>
    let m := π (π (k * n))
    m.sqrt ^ 2 = m

theorem t (n : ℕ) (hn : n > 0) : a n > 0 := by
  simpa [a] using hn
