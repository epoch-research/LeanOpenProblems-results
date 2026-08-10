import FormalConjectures.Util.ProblemImports

open Nat

theorem dvd_of_dvd_mul_and_gcd_dvd_dual_int (d Y A C : ℤ) (h1 : d ∣ A * Y) (h2 : (Int.gcd d Y : ℤ) ∣ C) : d ∣ A * C := by
  have h_bezout : (Int.gcd d Y : ℤ) = d * Int.gcdA d Y + Y * Int.gcdB d Y := by
    exact Int.gcd_eq_gcd_ab d Y
  have h_mul : A * (Int.gcd d Y : ℤ) = A * d * Int.gcdA d Y + A * Y * Int.gcdB d Y := by
    calc A * (Int.gcd d Y : ℤ)
      _ = A * (d * Int.gcdA d Y + Y * Int.gcdB d Y) := by rw [h_bezout]
      _ = A * d * Int.gcdA d Y + A * Y * Int.gcdB d Y := by ring
  have h_dvd_left : d ∣ A * d * Int.gcdA d Y := by
    use A * Int.gcdA d Y
    ring
  have h_dvd_right : d ∣ A * Y * Int.gcdB d Y := by
    rcases h1 with ⟨q, hq⟩
    use q * Int.gcdB d Y
    rw [hq]
    ring
  have h_dvd_sum : d ∣ A * (Int.gcd d Y : ℤ) := by
    rw [h_mul]
    exact dvd_add h_dvd_left h_dvd_right
  have h_C_dvd : A * (Int.gcd d Y : ℤ) ∣ A * C := mul_dvd_mul_left A h2
  exact dvd_trans h_dvd_sum h_C_dvd

#check padicValNat_factorial