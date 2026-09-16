import Mathlib

open Nat Finset

lemma valid_period_n (p n k : ℕ) :
  (k + n)^p % n = k^p % n := by
  have : (k + n) % n = k % n := Nat.add_mod_right k n
  -- mod_pow or something?
  exact Nat.ModEq.pow p this
