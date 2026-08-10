import FormalConjectures.Util.ProblemImports

open Nat Set

noncomputable def a354747 (n : ℕ) : ℕ :=
  let prime_steps : Set ℕ :=
    { m : ℕ | m > 0 ∧ Nat.Prime (2 * n * 3 ^ m - 1) }
  sInf prime_steps

example : a354747 100943 = 0 := by
  unfold a354747
  rw [Nat.sInf_eq_zero]
  right
  ext m
  simp
  native_decide +revert
