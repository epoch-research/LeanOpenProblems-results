import FormalConjectures.Util.ProblemImports

open Nat

def modify_range (L R : Nat) (arr : Array Nat) (f : Nat → Nat) : Array Nat :=
  if L > R then arr
  else if L = R then arr.set! L (f L)
  else
    let mid := (L + R) / 2
    let arr' := modify_range L mid arr f
    modify_range (mid + 1) R arr' f

def init_totients (max_n : Nat) : Array Nat :=
  let arr := Array.mkArray (max_n + 1) 0
  modify_range 0 max_n arr id

theorem test_init : (init_totients 100000)[99999]! = 99999 := by
  decide
