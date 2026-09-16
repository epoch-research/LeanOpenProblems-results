import FormalConjectures.Util.ProblemImports

theorem test (n m : ℕ) (h : (n:ℤ) + 1 = Int.ofNat m) : n = (Int.ofNat m - 1).toNat :=
by
  omega
