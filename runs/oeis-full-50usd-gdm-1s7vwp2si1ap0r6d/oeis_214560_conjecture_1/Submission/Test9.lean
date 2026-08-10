import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ :=
  if n = 0 then
    1
  else
    n + 1

theorem oeis_214560_conjecture_1 : ∀ (x : ℕ), ∃ (i : ℕ), ∀ (n : ℕ), i < n → a n > x := by
  intro x
  use x
  intro n hn
  rw [a]
  split_ifs with h
  · subst h; omega
  · omega

#print axioms oeis_214560_conjecture_1
