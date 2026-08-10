import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

example (n : ℕ) (h : n > 13) : A216265 n > 0 := by
  unfold A216265
  -- try a batch of possible tactics, each isolated below in comments during manual tests
  first
  | omega
  | nlinarith
  | norm_num
  | simp
  | aesop
  | grind
  | positivity

example (n : ℕ) (h : n > 13) : A216265 n > 0 := by
  unfold A216265 Nat.primeCounting Nat.primeCounting'
  first
  | omega
  | simp
  | aesop
  | grind
