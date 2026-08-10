import FormalConjectures.Util.ProblemImports

/--
A214560: Number of 0's in binary expansion of $n^2$.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then
    1
  else
    (Nat.digits 2 (n ^ 2)).count 0

theorem oeis_214560_conjecture_1 : ∀ (x : ℕ), ∃ (i : ℕ), ∀ (n : ℕ), i < n → a n > x :=
  answer(sorry)

#print axioms oeis_214560_conjecture_1
