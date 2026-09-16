import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ :=
  (Nat.digits 10 (n ^ 3)).min?.getD 0

theorem oeis_333206_conjecture_infiniteness_a_ge_five :
  ∀ (M : ℕ), ∃ (n : ℕ), M ≤ n ∧ 5 ≤ a n :=
  sorry

theorem oeis_333206_conjecture_infiniteness_a_ge_five.disproof : ¬ (type_of% @oeis_333206_conjecture_infiniteness_a_ge_five) := 
  sorry
