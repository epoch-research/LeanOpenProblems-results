import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def S (n : ℕ) : Set ℕ := {k : ℕ | Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)}
noncomputable def A (n : ℕ) : ℕ := sInf (S n)

example (n : ℕ) : A n ∈ S n := by
  unfold A S
  -- should require nonempty
  fail_if_success exact Nat.sInf_mem ?_
  simp?

example (n : ℕ) : ∃ k, k ∈ S n := by
  use A n
  unfold A S
  -- should fail
  simp?
