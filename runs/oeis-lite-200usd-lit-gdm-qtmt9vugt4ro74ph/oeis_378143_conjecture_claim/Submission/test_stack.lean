import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

set_option exponentiation.threshold 30000000
set_option maxRecDepth 10000

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

abbrev M_val : ℕ := 10 ^ (2 ^ 21) + 1

#eval f21 (3 : ZMod M_val)
