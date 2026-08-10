import FormalConjectures.Util.ProblemImports

theorem omega_test (n : ℕ) (an an1 an2 : ℕ)
    (h_mod : n % 6 = 1)
    (h_an : an / 12 = 2 * n - 1)
    (h_an1 : an1 % 72 = 0)
    (h_an2 : an2 % 72 = 36) :
    6 ∣ (((an1) / 12 : ℤ) - ((n - 1) : ℤ)) ∧
    6 ∣ (((an) / 12 : ℤ) - (n : ℤ)) ∧
    6 ∣ (((an2) / 12 : ℤ) - ((n + 2) : ℤ)) := by
  omega
