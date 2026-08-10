import FormalConjectures.Util.ProblemImports

lemma test_omega_d9 (q X : ℤ) (hX : 0 < X)
    (h1 : 3141592653589793238462638 * 100 * X < 1000 * q + 100 * 9)
    (h2 : 1000 * q + 100 * 9 < 3141592653589793238462652 * 100 * X) : False := by
  omega
