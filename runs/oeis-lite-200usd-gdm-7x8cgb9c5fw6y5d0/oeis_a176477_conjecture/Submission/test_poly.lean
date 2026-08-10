import FormalConjectures.Util.ProblemImports

lemma poly_identity (n : ℤ) :
  (21 * (n+1) ^ 3 + 22 * (n+1) ^ 2 + 8 * (n+1) + 1) - (n+1) ^ 3 * (4 * n + 5) ^ 2 =
  (-2 * n ^ 2 - 2 * n + 1) * (2 * n + 3) ^ 3 := by ring
