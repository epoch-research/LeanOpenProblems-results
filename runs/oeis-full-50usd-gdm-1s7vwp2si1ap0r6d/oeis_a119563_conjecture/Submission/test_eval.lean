import Mathlib.Data.ZMod.Basic

open Nat

set_option exponentiation.threshold 100000

def val : ℕ := 2 ^ 32768 + 32767

#eval (3 : ZMod val) ^ (2 ^ 32768 + 32766)
