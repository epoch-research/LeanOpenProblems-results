import Submission.Spec
open Padic

theorem test_zero (p n : ℕ) [Fact p.Prime] (hp : p > 3) (hn : 0 < n) :
    (Nat.cast (p * n) : Padic p) ^ 2 ≠ 0 := by
  intro h
  have h1 : (Nat.cast (p * n) : Padic p) = 0 := pow_eq_zero h
  sorry
