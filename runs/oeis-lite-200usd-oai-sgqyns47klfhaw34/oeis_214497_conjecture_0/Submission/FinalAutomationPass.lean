import FormalConjectures.Util.ProblemImports

open Nat

example (n : ℕ) (hn : n > 0) :
    ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1) := by
  classical
  try exact?
  try apply?
  try aesop
  try omega
  try grind
  try simp_all
  fail

example :
  ¬ (∀ n : ℕ, n > 0 →
      ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)) := by
  classical
  try exact?
  try apply?
  try aesop
  try omega
  try grind
  try simp_all
  fail
