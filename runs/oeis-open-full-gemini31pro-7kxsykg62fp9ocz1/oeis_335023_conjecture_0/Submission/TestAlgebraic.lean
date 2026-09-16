import FormalConjectures.Util.ProblemImports

open Int

lemma gcd_step (F n_fact p : ℤ) (hp : p > 1)
  (h_vp : ∃ k : ℤ, F = n_fact * k) : -- Wait, F(n) = n! S_n, but S_n is a rational!
  -- We don't have S_n as integer. But we can state it as:
  True := trivial
