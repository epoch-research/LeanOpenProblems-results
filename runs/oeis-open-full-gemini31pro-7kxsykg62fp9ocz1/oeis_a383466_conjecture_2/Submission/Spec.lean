import FormalConjectures.Util.ProblemImports
open Set

def a : ℕ → ℕ
  | 0 => 1
  | k + 1 => 5 * (k + 1) * (2 * (k + 1) - 1) + 2

noncomputable section

axiom pentagram_configuration (n : ℕ) : Type
axiom number_of_regions {n : ℕ} (C : pentagram_configuration n) : ℕ

theorem oeis_a383466_conjecture_2 (n : ℕ) :
  a n = sSup (Set.range (@number_of_regions n)) := by
  sorry

end

theorem oeis_a383466_conjecture_2.disproof : ¬ (type_of% @oeis_a383466_conjecture_2) := answer(
  fun _ => by sorry
)
