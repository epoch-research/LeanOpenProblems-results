import Mathlib

open Nat

lemma div_odd_mod_two (A B : ℕ) (hB : B % 2 = 1) (h_dvd : B ∣ A) : (A / B) % 2 = A % 2 := by
  rcases h_dvd with ⟨q, rfl⟩
  rw [Nat.mul_div_cancel_left _ (by omega)]
  rw [Nat.mul_mod, hB]
  simp
