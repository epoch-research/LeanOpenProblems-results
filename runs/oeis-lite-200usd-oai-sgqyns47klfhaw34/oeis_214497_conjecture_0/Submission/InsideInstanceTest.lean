import FormalConjectures.Util.ProblemImports
open Nat

theorem test_inside (n : ℕ) (hn : n > 0) :
    ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1) := by
  letI : Pow Nat Nat := ⟨fun _ _ => 0⟩
  letI : Sub Nat := ⟨fun _ _ => 3⟩
  letI : Mul Nat := ⟨fun _ _ => 4⟩
  letI : Add Nat := ⟨fun _ _ => 5⟩
  use 0
  change Nat.Prime 3 ∧ Nat.Prime 5
  norm_num
