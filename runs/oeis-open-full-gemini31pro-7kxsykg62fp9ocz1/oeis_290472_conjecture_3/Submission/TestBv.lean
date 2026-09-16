import Mathlib

theorem test (x : BitVec 32) : x + 0 = x := by bv_decide
#print axioms test
