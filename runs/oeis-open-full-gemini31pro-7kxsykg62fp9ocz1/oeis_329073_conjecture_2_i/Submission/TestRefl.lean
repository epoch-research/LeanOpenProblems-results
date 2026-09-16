import Mathlib

example : ¬ ((430 : ℤ) % 2 = 1 ↔ Nat.isPowerOfTwo 3) := by
  intro h
  have h1 : (430 : ℤ) % 2 ≠ 1 := by decide
  have h2 : ¬ Nat.isPowerOfTwo 3 := by
    rintro ⟨k, hk⟩
    omega
  -- oops, we want to prove it IS true?
  -- 430 % 2 is 0. 0 = 1 is False.
  -- isPowerOfTwo 3 is False.
  -- False ↔ False is True!
  -- So my disproof was WRONG if I used n=3!
