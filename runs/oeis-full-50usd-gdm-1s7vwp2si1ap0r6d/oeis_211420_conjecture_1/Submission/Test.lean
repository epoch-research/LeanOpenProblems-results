import FormalConjectures.Util.ProblemImports

open Nat

theorem dvd_factorial_of_ge (n r : ℕ) (h : 8 * n ≥ 2 * r + 1) :
    ((8 * n - (2 * r + 1) : ℕ) : ℤ) ∣ ((8 * n).factorial : ℤ) := by
  have h1 : 0 < 8 * n - (2 * r + 1) := by omega
  have h2 : 8 * n - (2 * r + 1) ≤ 8 * n := by omega
  have h_dvd := Nat.dvd_factorial h1 h2
  exact_mod_cast h_dvd

#check padicValNat_factorial
