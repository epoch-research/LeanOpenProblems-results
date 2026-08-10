import FormalConjectures.Util.ProblemImports
#check Nat.odd_iff
#check Nat.not_even_iff_odd
#check Nat.even_iff
#check Nat.Odd
#check Odd
#check Nat.two_dvd_ne_zero
example {q : ℕ} (h : q % 2 = 1) : Odd q := by
  rw [← Nat.not_even_iff_odd]
  intro he
  rw [Nat.even_iff] at he
  omega
