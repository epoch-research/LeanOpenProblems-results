import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

set_option exponentiation.threshold 30000000
set_option maxRecDepth 5000000

open Nat ZMod

variable {M : ℕ}

def f0 (x : ZMod M) : ZMod M := x ^ 10
def f1 (x : ZMod M) : ZMod M := f0 (f0 x)
def f2 (x : ZMod M) : ZMod M := f1 (f1 x)
def f3 (x : ZMod M) : ZMod M := f2 (f2 x)
def f4 (x : ZMod M) : ZMod M := f3 (f3 x)
def f5 (x : ZMod M) : ZMod M := f4 (f4 x)
def f6 (x : ZMod M) : ZMod M := f5 (f5 x)
def f7 (x : ZMod M) : ZMod M := f6 (f6 x)
def f8 (x : ZMod M) : ZMod M := f7 (f7 x)
def f9 (x : ZMod M) : ZMod M := f8 (f8 x)
def f10 (x : ZMod M) : ZMod M := f9 (f9 x)
def f11 (x : ZMod M) : ZMod M := f10 (f10 x)
def f12 (x : ZMod M) : ZMod M := f11 (f11 x)
def f13 (x : ZMod M) : ZMod M := f12 (f12 x)
def f14 (x : ZMod M) : ZMod M := f13 (f13 x)
def f15 (x : ZMod M) : ZMod M := f14 (f14 x)
def f16 (x : ZMod M) : ZMod M := f15 (f15 x)
def f17 (x : ZMod M) : ZMod M := f16 (f16 x)
def f18 (x : ZMod M) : ZMod M := f17 (f17 x)
def f19 (x : ZMod M) : ZMod M := f18 (f18 x)
def f20 (x : ZMod M) : ZMod M := f19 (f19 x)
def f21 (x : ZMod M) : ZMod M := f20 (f20 x)

theorem f0_eq (x : ZMod M) : f0 x = x ^ (10 ^ (2 ^ 0)) := rfl

theorem f1_eq (x : ZMod M) : f1 x = x ^ (10 ^ (2 ^ 1)) := by
  change f0 (f0 x) = _
  rw [f0_eq, f0_eq]
  rw [← pow_mul]
  congr 1

theorem f2_eq (x : ZMod M) : f2 x = x ^ (10 ^ (2 ^ 2)) := by
  change f1 (f1 x) = _
  rw [f1_eq, f1_eq]
  rw [← pow_mul]
  congr 1

theorem f3_eq (x : ZMod M) : f3 x = x ^ (10 ^ (2 ^ 3)) := by
  change f2 (f2 x) = _
  rw [f2_eq, f2_eq]
  rw [← pow_mul]
  congr 1

theorem f4_eq (x : ZMod M) : f4 x = x ^ (10 ^ (2 ^ 4)) := by
  change f3 (f3 x) = _
  rw [f3_eq, f3_eq]
  rw [← pow_mul]
  congr 1

theorem f5_eq (x : ZMod M) : f5 x = x ^ (10 ^ (2 ^ 5)) := by
  change f4 (f4 x) = _
  rw [f4_eq, f4_eq]
  rw [← pow_mul]
  congr 1

theorem f6_eq (x : ZMod M) : f6 x = x ^ (10 ^ (2 ^ 6)) := by
  change f5 (f5 x) = _
  rw [f5_eq, f5_eq]
  rw [← pow_mul]
  congr 1

theorem f7_eq (x : ZMod M) : f7 x = x ^ (10 ^ (2 ^ 7)) := by
  change f6 (f6 x) = _
  rw [f6_eq, f6_eq]
  rw [← pow_mul]
  congr 1

theorem f8_eq (x : ZMod M) : f8 x = x ^ (10 ^ (2 ^ 8)) := by
  change f7 (f7 x) = _
  rw [f7_eq, f7_eq]
  rw [← pow_mul]
  congr 1

theorem f9_eq (x : ZMod M) : f9 x = x ^ (10 ^ (2 ^ 9)) := by
  change f8 (f8 x) = _
  rw [f8_eq, f8_eq]
  rw [← pow_mul]
  congr 1

theorem f10_eq (x : ZMod M) : f10 x = x ^ (10 ^ (2 ^ 10)) := by
  change f9 (f9 x) = _
  rw [f9_eq, f9_eq]
  rw [← pow_mul]
  congr 1

theorem f11_eq (x : ZMod M) : f11 x = x ^ (10 ^ (2 ^ 11)) := by
  change f10 (f10 x) = _
  rw [f10_eq, f10_eq]
  rw [← pow_mul]
  congr 1

theorem f12_eq (x : ZMod M) : f12 x = x ^ (10 ^ (2 ^ 12)) := by
  change f11 (f11 x) = _
  rw [f11_eq, f11_eq]
  rw [← pow_mul]
  congr 1

theorem f13_eq (x : ZMod M) : f13 x = x ^ (10 ^ (2 ^ 13)) := by
  change f12 (f12 x) = _
  rw [f12_eq, f12_eq]
  rw [← pow_mul]
  congr 1

theorem f14_eq (x : ZMod M) : f14 x = x ^ (10 ^ (2 ^ 14)) := by
  change f13 (f13 x) = _
  rw [f13_eq, f13_eq]
  rw [← pow_mul]
  congr 1

theorem f15_eq (x : ZMod M) : f15 x = x ^ (10 ^ (2 ^ 15)) := by
  change f14 (f14 x) = _
  rw [f14_eq, f14_eq]
  rw [← pow_mul]
  congr 1

theorem f16_eq (x : ZMod M) : f16 x = x ^ (10 ^ (2 ^ 16)) := by
  change f15 (f15 x) = _
  rw [f15_eq, f15_eq]
  rw [← pow_mul]
  congr 1

theorem f17_eq (x : ZMod M) : f17 x = x ^ (10 ^ (2 ^ 17)) := by
  change f16 (f16 x) = _
  rw [f16_eq, f16_eq]
  rw [← pow_mul]
  congr 1

theorem f18_eq (x : ZMod M) : f18 x = x ^ (10 ^ (2 ^ 18)) := by
  change f17 (f17 x) = _
  rw [f17_eq, f17_eq]
  rw [← pow_mul]
  congr 1

theorem f19_eq (x : ZMod M) : f19 x = x ^ (10 ^ (2 ^ 19)) := by
  change f18 (f18 x) = _
  rw [f18_eq, f18_eq]
  rw [← pow_mul]
  congr 1

theorem f20_eq (x : ZMod M) : f20 x = x ^ (10 ^ (2 ^ 20)) := by
  change f19 (f19 x) = _
  rw [f19_eq, f19_eq]
  rw [← pow_mul]
  congr 1

theorem f21_eq (x : ZMod M) : f21 x = x ^ (10 ^ (2 ^ 21)) := by
  change f20 (f20 x) = _
  rw [f20_eq, f20_eq]
  rw [← pow_mul]
  congr 1

theorem lemma_21 : (3 : ZMod (10 ^ (2 ^ 21) + 1)) ^ (10 ^ (2 ^ 21)) ≠ 1 := by
  rw [← f21_eq]
  decide
