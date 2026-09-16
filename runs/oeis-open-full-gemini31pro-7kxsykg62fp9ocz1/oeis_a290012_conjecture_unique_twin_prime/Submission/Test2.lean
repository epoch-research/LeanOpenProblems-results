import Mathlib

def nthPrime (n : ℕ) : ℕ :=
  if n = 0 then 2
  else if n = 1 then 3
  else if n = 2 then 5
  else if n = 3 then 7
  else if n = 4 then 11
  else if n = 5 then 13
  else 0

lemma nthPrime_eq_nth (n : ℕ) (h : n ≤ 5) : nthPrime n = Nat.nth Nat.Prime n := by
  sorry
