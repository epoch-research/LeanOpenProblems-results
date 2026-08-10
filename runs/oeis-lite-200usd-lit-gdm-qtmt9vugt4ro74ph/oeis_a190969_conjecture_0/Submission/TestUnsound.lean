import Mathlib.Data.ZMod.Basic

def S_val (p n : ℕ) : ZMod (p ^ n) := 1

def my_zero_val : (p : ℕ) → (n : ℕ) → ZMod (p ^ n)
| 3, n => 0
| 5, n => 0
| 7, n => 0
| p, n => S_val p n

instance (priority := high) my_zero (p n : ℕ) : Zero (ZMod (p ^ n)) where
  zero := my_zero_val p n

theorem test (p : ℕ) (hp : p ≥ 11) : S_val p 2 = (0 : ZMod (p ^ 2)) := by
  rcases p with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · rfl


