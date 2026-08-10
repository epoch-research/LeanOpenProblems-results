import FormalConjectures.Util.ProblemImports

noncomputable def a (n : ℕ) : ℕ :=
  let start_idx : ℕ := (n * (n - 1)) / 2
  Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime (start_idx + i)

#check Nat.Prime.eq_two_or_odd
#check Nat.Prime.odd_of_ne_two
#check Nat.even_iff
#check Nat.Even
#check Odd
#check even_iff_two_dvd
#check Nat.odd_iff
#check Finset.sum_mod
