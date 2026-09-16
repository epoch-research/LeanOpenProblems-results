import FormalConjectures.Util.ProblemImports
open Int

lemma gcd_div_sq (n x y : ℤ) : gcd (n * x + y) (n * y) ∣ n^2 * gcd x y := by
  have h1 : gcd (n * x + y) (n * y) ∣ n * (n * x + y) := dvd_mul_left _ _
  -- Wait, Int.gcd_dvd_left etc
  sorry
