import Mathlib

def S : List ℕ := [1, 17, 19, 323] -- partial list just to test syntax

def check_all_d (n : ℕ) : Bool :=
  let rec loop (d : ℕ) : Bool :=
    if d > n then true
    else if n % d == 0 then
      if S.contains d then loop (d + 1)
      else false
    else loop (d + 1)
  loop 1

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

theorem t : check_all_d 6678671 = false := by decide
