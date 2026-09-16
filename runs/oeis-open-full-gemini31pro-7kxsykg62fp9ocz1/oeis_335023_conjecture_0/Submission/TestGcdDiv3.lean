import FormalConjectures.Util.ProblemImports
open Int

lemma gcd_div_sq (n x y : ℤ) : (Int.gcd (n * x + y) (n * y) : ℤ) ∣ n^2 * (Int.gcd x y : ℤ) := by
  have h1 : (Int.gcd (n * x + y) (n * y) : ℤ) ∣ n * (n * x + y) := dvd_mul_of_dvd_right (gcd_dvd_left _ _) n
  have h2 : (Int.gcd (n * x + y) (n * y) : ℤ) ∣ n * y := gcd_dvd_right _ _
  have h3 : (Int.gcd (n * x + y) (n * y) : ℤ) ∣ (n^2 * x) := by
    have : n^2 * x = n * (n * x + y) - n * y := by ring
    rw [this]
    exact dvd_sub h1 h2
  have h4 : (Int.gcd (n * x + y) (n * y) : ℤ) ∣ (n^2 * y) := by
    have : n^2 * y = n * (n * y) := by ring
    rw [this]
    exact dvd_mul_of_dvd_right h2 n
  have h5 : (Int.gcd (n * x + y) (n * y) : ℤ) ∣ Int.gcd (n^2 * x) (n^2 * y) := dvd_gcd h3 h4
  have h6 : (Int.gcd (n^2 * x) (n^2 * y) : ℤ) = (n^2).natAbs * (Int.gcd x y : ℤ) := by
    sorry
  sorry
