import FormalConjectures.Util.ProblemImports

open Nat

def sqrt_binary_loop (m : Nat) : Nat → Nat → Nat → Nat
  | 0, _, high => high
  | fuel + 1, low, high =>
    if low > high then high
    else
      let mid := (low + high) / 2
      let sq := mid * mid
      if sq = m then mid
      else if sq > m then
        if mid == 0 then low
        else sqrt_binary_loop m fuel low (mid - 1)
      else
        sqrt_binary_loop m fuel (mid + 1) high

def sqrt_fast (m : Nat) : Nat :=
  sqrt_binary_loop m 40 0 m

theorem test_sqrt1 : sqrt_fast 1000000000 = 31622 := by
  decide

theorem test_sqrt2 : sqrt_fast 9 = 3 := by
  decide

theorem test_sqrt3 : sqrt_fast 10 = 3 := by
  decide
