import Mathlib.Data.Nat.Basic

def powMod (base exp mod : ℕ) : ℕ :=
  if h : exp = 0 then 1 % mod
  else
    have : exp / 2 < exp := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
    if exp % 2 = 1 then
      (base * powMod (base * base % mod) (exp / 2) mod) % mod
    else
      powMod (base * base % mod) (exp / 2) mod
termination_by exp
