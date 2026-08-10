import FormalConjectures.Util.ProblemImports

/--
A333206: $a(n)$ is the least decimal digit of $n^3$.
-/
def a (n : ℕ) : ℕ :=
  (Nat.digits 10 (n ^ 3)).min?.getD 0



/--
This theorem formalizes the contrapositive of the previous claim based on the heuristic:
that there are infinitely many $n$ such that $a(n) \ge 5$.
-/
theorem oeis_333206_conjecture_infiniteness_a_ge_five :
  ∀ (M : ℕ), ∃ (n : ℕ), M ≤ n ∧ 5 ≤ a n := by
  intro M
  use M

#print axioms oeis_333206_conjecture_infiniteness_a_ge_five

