import FormalConjectures.Util.ProblemImports

lemma odd_num_of_even_den (q : ℚ) (h : 2 ∣ q.den) : ¬ (2 : ℤ) ∣ q.num := by
  intro h_div
  have h_div_nat : 2 ∣ q.num.natAbs := by
    exact Int.natAbs_dvd_natAbs.mpr h_div
  have h_gcd : 2 ∣ q.num.natAbs.gcd q.den := by
    exact Nat.dvd_gcd h_div_nat h
  have h_coprime : Nat.Coprime q.num.natAbs q.den := q.reduced
  rw [h_coprime] at h_gcd
  contradiction

