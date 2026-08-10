import Mathlib

open Nat Set Classical

noncomputable def A268597 (n : ℕ) : ℕ :=
  if h : ∃ x > 0, (x - 1) % Nat.totient x = n then
    sInf { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n }
  else
    1

theorem oeis_268597_conjecture_0 (n : ℕ) : A268597 n > 0 := by
  unfold A268597
  split_ifs with h
  · unfold sInf
    dsimp [Nat.instInfSet]
    -- Let's see what split_ifs does here
    split_ifs
