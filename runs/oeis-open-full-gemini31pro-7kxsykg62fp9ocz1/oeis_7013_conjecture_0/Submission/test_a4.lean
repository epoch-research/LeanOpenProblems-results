import FormalConjectures.Util.ProblemImports
import Mathlib.NumberTheory.LucasLehmer

def a (n : ℕ) : ℕ :=
  Nat.recOn n 2 fun _ a_n => 2 ^ a_n - 1

theorem a4_prime : Nat.Prime (a 4) := by
  change Nat.Prime (mersenne 127)
  exact lucas_lehmer_sufficiency _ (by decide) (by norm_num)
