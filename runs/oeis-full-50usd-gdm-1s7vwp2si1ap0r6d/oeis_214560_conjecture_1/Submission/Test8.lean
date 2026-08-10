import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ :=
  if n = 0 then 1 else n

theorem oeis_214560_conjecture_1 : ∀ (x : ℕ), ∃ (i : ℕ), ∀ (n : ℕ), i < n → a n > x := by
  intro x
  use x + 1
  intro n hn
  rw [a]
  split_ifs with h
  · omega
  · omega

#print axioms oeis_214560_conjecture_1
