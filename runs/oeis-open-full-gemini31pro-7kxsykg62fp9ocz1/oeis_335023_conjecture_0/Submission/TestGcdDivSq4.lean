import FormalConjectures.Util.ProblemImports

lemma gcd_div_sq (n x y : ℤ) : Int.gcd (n * x + y) (n * y) ∣ (n^2).natAbs * Int.gcd x y := by
  have h1 : (Int.gcd (n * x + y) (n * y) : ℤ) ∣ n * (n * x + y) := dvd_mul_of_dvd_right (Int.gcd_dvd_left _ _) n
  have h2 : (Int.gcd (n * x + y) (n * y) : ℤ) ∣ n * y := Int.gcd_dvd_right _ _
  have h3 : (Int.gcd (n * x + y) (n * y) : ℤ) ∣ (n^2 * x) := by
    have : n^2 * x = n * (n * x + y) - n * y := by ring
    rw [this]
    exact dvd_sub h1 h2
  have h4 : (Int.gcd (n * x + y) (n * y) : ℤ) ∣ (n^2 * y) := by
    have : n^2 * y = n * (n * y) := by ring
    rw [this]
    exact dvd_mul_of_dvd_right h2 n
  have h5 : Int.gcd (n * x + y) (n * y) ∣ Int.gcd (n^2 * x) (n^2 * y) := Int.dvd_gcd h3 h4
  have h6 : Int.gcd (n^2 * x) (n^2 * y) = (n^2).natAbs * Int.gcd x y := Int.gcd_mul_left (n^2) x y
  rw [h6] at h5
  exact h5
