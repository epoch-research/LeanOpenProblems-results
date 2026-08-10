import FormalConjectures.Util.ProblemImports

example (n : ℕ) (h : n % 3 = 1) : 3 ∣ 128*n - 152 := by
  omega
example (n : ℕ) (h : n % 3 = 1) : 3 ∣ 4*n - 1 := by
  omega
example (n : ℕ) (hn : 3 ≤ n) (h : n % 3 = 0) : 3 ∣ 2*n - 3 := by
  omega
example (n : ℕ) (hn : 3 ≤ n) (h : n % 3 = 2) : 3 ∣ 2*n - 1 := by
  omega
example (n : ℕ) (hn : 3 ≤ n) (h : n % 3 ≠ 1) : 3 ∣ (2*n-3)*(2*n-1) := by
  have hm : n % 3 < 3 := Nat.mod_lt n (by decide)
  interval_cases h0 : n % 3
  · exact dvd_mul_of_dvd_left (by omega : 3 ∣ 2*n-3) _
  · contradiction
  · exact dvd_mul_of_dvd_right (by omega : 3 ∣ 2*n-1) _
