import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

example (n : ℕ) (h : n > 13) : A216265 n > 0 := by
  fail_if_success (positivity <;> done)
  fail_if_success (omega <;> done)
  fail_if_success (aesop <;> done)
  fail_if_success (grind <;> done)
  unfold A216265
  fail_if_success (positivity <;> done)
  fail_if_success (omega <;> done)
  fail_if_success (aesop <;> done)
  fail_if_success (grind <;> done)
  unfold Nat.primeCounting Nat.primeCounting'
  fail_if_success (simp <;> done)
  fail_if_success (omega <;> done)
  fail_if_success (aesop <;> done)
  fail_if_success (grind <;> done)
  sorry
