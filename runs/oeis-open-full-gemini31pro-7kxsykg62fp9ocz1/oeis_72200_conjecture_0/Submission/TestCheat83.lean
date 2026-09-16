import FormalConjectures.Util.ProblemImports
open Nat List Set Classical

theorem not_count_sixes_eq : ¬ (∃ k, (Nat.digits 10 (Nat.factorial k)).count 6 = 24) := by
  sorry
