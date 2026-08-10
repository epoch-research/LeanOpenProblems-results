import FormalConjectures.Util.ProblemImports

theorem test_omega (n : ℕ)
    (h_lt : 2 * n + 1 < 462120945)
    (h3 : (2 * n + 1) % 3 = 0)
    (h5 : (2 * n + 1) % 5 = 0)
    (h11 : (2 * n + 1) % 11 = 0)
    (h13 : (2 * n + 1) % 13 = 0)
    (h19 : (2 * n + 1) % 19 = 0)
    (h29 : (2 * n + 1) % 29 = 0)
    (h17 : (2 * n + 1) % 17 = 0)
    (h23 : (2 * n + 1) % 23 = 0) : n = 231060472 := by
  omega
