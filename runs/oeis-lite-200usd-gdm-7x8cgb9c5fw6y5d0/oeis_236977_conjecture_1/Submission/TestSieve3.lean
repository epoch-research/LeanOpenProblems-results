import FormalConjectures.Util.ProblemImports

open Nat

def init_array_range (L R : Nat) (arr : Array Nat) : Array Nat :=
  if L > R then arr
  else if L = R then arr.set! L L
  else
    let mid := (L + R) / 2
    let arr' := init_array_range L mid arr
    init_array_range (mid + 1) R arr'

def init_totients (max_n : Nat) : Array Nat :=
  let arr := Array.mkArray (max_n + 1) 0
  init_array_range 0 max_n arr

def update_multiples (p : Nat) (i : Nat) (step : Nat) (limit : Nat) (arr : Array Nat) : Array Nat :=
  if i > limit then arr
  else
    let val := arr.get! i
    let val' := val - val / p
    let arr' := arr.set! i val'
    update_multiples p (i + step) step limit arr'

def sieve_loop (p : Nat) (limit : Nat) (arr : Array Nat) : Array Nat :=
  if p > limit then arr
  else
    let val := arr.get! p
    if val == p then
      let arr' := update_multiples p p p limit arr
      sieve_loop (p + 1) limit arr'
    else
      sieve_loop (p + 1) limit arr

def sieve_totients (max_n : Nat) : Array Nat :=
  let arr := init_totients max_n
  sieve_loop 2 max_n arr

theorem test_sieve : (sieve_totients 100000)[99999]! = 64800 := by
  decide
