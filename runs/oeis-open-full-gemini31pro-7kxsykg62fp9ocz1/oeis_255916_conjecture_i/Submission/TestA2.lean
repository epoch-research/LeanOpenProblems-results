import Submission.Spec
open Nat Int

def check_a (n : ℕ) : Bool :=
  Id.run do
    let bound : ℕ := n + 1
    for z_idx in [0 : 2 * bound + 1] do
      let z : ℤ := (z_idx : ℤ) - (bound : ℤ)
      for x in [0 : bound] do
        for y in [0 : bound] do
          let g := ((5 * z^2 - 3 * z) / 2).toNat
          let p8 := x * (3 * x - 2)
          let p9 := y * (7 * y - 5) / 2
          if g + p8 + p9 == n then
            return true
    return false

def check_all_a : IO Unit := do
  for n in [0 : 100] do
    if not (check_a n) then
      IO.println s!"Failed a n > 0 at {n}"
      return
  IO.println "All passed."

#eval check_all_a
