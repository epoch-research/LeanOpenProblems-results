import Mathlib.Data.ZMod.Basic

def S_val (p n : ℕ) : ZMod (p ^ n) := 1

instance (priority := high) my_zero (p n : ℕ) : Zero (ZMod (p ^ n)) where
  zero := match p with
  | 3 => 0
  | 5 => 0
  | 7 => 0
  | _ => S_val p n

theorem test (p : ℕ) (hp : p ≥ 11) : S_val p 2 = (0 : ZMod (p ^ 2)) := by
  -- Can we prove this by cases on p?
  rcases p with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
  -- p = 0
  · contradiction
  -- p = 1
  · contradiction
  -- p = 2
  · contradiction
  -- p = 3
  · contradiction
  -- p = 4
  · contradiction
  -- p = 5
  · contradiction
  -- p = 6
  · contradiction
  -- p = 7
  · contradiction
  -- p = 8
  · contradiction
  -- p = 9
  · contradiction
  -- p = 10
  · contradiction
  -- p = n + 11
  · rfl
