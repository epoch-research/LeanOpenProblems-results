import FormalConjectures.Util.ProblemImports

theorem test_omega (k : ℕ) (n : ℕ) (d3 : ℕ) (u3 : ℕ)
    (hk : k ≥ 5)
    (hn : n < 10^k - 1)
    (hd3 : d3 = Nat.gcd n (10^(k-3)))
    (hu3 : u3 = n / d3)
    (h_gcd_lt : ¬ u3 / Nat.gcd u3 100 < 10000) :
    k ≥ 6 := by
  omega
