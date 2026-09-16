import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  card ((Icc 1 n).filter fun k : ℕ => Nat.Prime (k ^ 4 + (2 * n + 1 - k) ^ 4))

theorem oeis_A218656_verified_range (n : ℕ) (hval : n ≤ 499999) (hn : 0 < n) : a n > 0 := sorry

#check (type_of% @oeis_A218656_verified_range)
