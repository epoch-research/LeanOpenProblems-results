import FormalConjectures.Util.ProblemImports

noncomputable def a (n : ℕ) : ℕ := n + 1

theorem test (n m : ℕ) (hz : (n:ℤ) + 0 = (m:ℤ)) : a n = if n < 10 then a m else a m :=
by
  (try split_ifs) <;> (try simp only [Int.ofNat_eq_natCast]) <;> (try congr 1) <;> omega
