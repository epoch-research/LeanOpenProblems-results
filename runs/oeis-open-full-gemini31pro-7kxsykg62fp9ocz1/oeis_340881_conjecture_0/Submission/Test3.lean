import Mathlib

lemma val_natCast_mod (p : ℕ) [hp : Fact p.Prime] (x : ℕ) :
    ZMod.val (x : ZMod p) = x % p := by rw [ZMod.val_natCast]
