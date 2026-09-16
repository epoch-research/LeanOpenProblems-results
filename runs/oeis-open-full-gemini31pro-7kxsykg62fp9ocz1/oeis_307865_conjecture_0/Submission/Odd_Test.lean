import Mathlib

open Nat

theorem odd_mod_two_eq_zero {u : ℕ} (hu_odd : Odd u) (hu_pos : 0 < u) (h2 : (2 : ZMod u) = 0) : u = 1 := by
  have h_dvd : u ∣ 2 := by
    rw [← CharP.cast_eq_zero_iff (ZMod u) u]
    exact h2
  have h_le : u ≤ 2 := Nat.le_of_dvd zero_lt_two h_dvd
  rcases hu_odd with ⟨k, hk⟩
  omega
