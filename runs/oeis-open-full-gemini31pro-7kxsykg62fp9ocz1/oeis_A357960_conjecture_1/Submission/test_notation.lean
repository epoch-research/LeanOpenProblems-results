import Mathlib

def MyModEq (a b c : ℕ) : Prop := True
local notation:50 a " ≡ " b " [MOD " c "]" => MyModEq a b c

theorem test (p : ℕ) : p ≡ p [MOD 5] := by trivial

#check test