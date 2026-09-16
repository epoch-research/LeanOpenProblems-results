import FormalConjectures.Util.ProblemImports
open Nat
def a (n : ℕ) : ℕ := n
def sequence_s_int (z : ℤ) : ℕ := if z < 1 then 0 else a (z - 1).toNat

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

theorem test : ∃ k : ℤ, ∀ n : ℕ, a n = sequence_s_int (n + k) :=
by
  use 1; intro n; generalize hz : (n:ℤ) + (1:ℤ) = z; cases z <;> rename_i m; { change (n:ℤ) + (1:ℤ) = (m:ℤ) at hz; try unfold sequence_s_int; try dsimp only [Int.ofNat_eq_natCast, Int.negSucc_eq]; try split_ifs <;> (try congr 1) <;> omega }; { change (n:ℤ) + (1:ℤ) = -(m + 1 : ℤ) at hz; try unfold sequence_s_int; try dsimp only [Int.ofNat_eq_natCast, Int.negSucc_eq]; try split_ifs <;> (try congr 1) <;> omega }

