import FormalConjectures.Util.ProblemImports

open Nat

theorem dvd_of_dvd_mul_and_gcd_dvd_dual (d Y A C : ℕ) (h1 : d ∣ A * Y) (h2 : Nat.gcd d Y ∣ C) : d ∣ A * C := by
  have h3 : d ∣ Nat.gcd (A * d) (A * Y) := Nat.dvd_gcd (dvd_mul_left d A) h1
  rw [Nat.gcd_mul_left A d Y] at h3
  have h4 : A * Nat.gcd d Y ∣ A * C := mul_dvd_mul_left A h2
  exact dvd_trans h3 h4
