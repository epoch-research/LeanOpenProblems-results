import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000
set_option maxHeartbeats 0
open Nat

def init_array_loop : Nat → Array Nat → Array Nat
  | 0, acc => acc
  | i + 1, acc => init_array_loop i (acc.push (acc.size))

def update_multiples_loop : Nat → Nat → Nat → Array Nat → Array Nat
  | 0, _, _, arr => arr
  | fuel + 1, p, i, arr =>
    if i < arr.size then
      let val := arr[i]!
      let val' := val - val / p
      let arr' := arr.set! i val'
      update_multiples_loop fuel p (i + p) arr'
    else
      arr

def sieve_loop : Nat → Nat → Array Nat → Array Nat
  | 0, _, arr => arr
  | fuel + 1, p, arr =>
    if p < arr.size then
      if arr[p]! == p then
        -- p is prime
        let update_fuel := arr.size / p + 1
        let arr' := update_multiples_loop update_fuel p p arr
        sieve_loop fuel (p + 1) arr'
      else
        sieve_loop fuel (p + 1) arr
    else
      arr

def sieve_totients (max_n : Nat) : Array Nat :=
  let arr := init_array_loop max_n Array.empty
  sieve_loop max_n 2 arr
theorem test_sieve : (sieve_totients 100000)[99999]! = 64800 := by
  decide
