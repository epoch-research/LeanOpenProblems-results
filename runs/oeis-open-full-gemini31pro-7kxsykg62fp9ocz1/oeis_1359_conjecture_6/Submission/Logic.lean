import Mathlib

open Nat Finset ZMod

lemma wilson_mod_eq (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (h_lt : p < q) (W : ℕ)
  (hW : (q - 1)! ≡ p! * W * (q - 1) [MOD q]) :
  p! ≡ 1 [MOD q] ↔ W ≡ 1 [MOD q] := by
  sorry
