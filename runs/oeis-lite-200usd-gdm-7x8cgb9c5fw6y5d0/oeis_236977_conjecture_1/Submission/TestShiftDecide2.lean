open Nat

def test1 : Nat := (1024 : Nat) >>> 2

#eval test1
theorem test_dec : (1024 : Nat) >>> 2 = 256 := by decide
