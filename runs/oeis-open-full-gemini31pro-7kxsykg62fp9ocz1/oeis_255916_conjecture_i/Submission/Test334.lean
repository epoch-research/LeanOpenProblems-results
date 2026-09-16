import Submission.Spec
open Nat Int

def G7 (k : ℤ) : ℕ := ((5 * k^2 - 3 * k) / 2).toNat
def P (m : ℕ) (x : ℕ) : ℕ :=
  let m' := (m : ℤ)
  let x' := (x : ℤ)
  let val := (m' - 2) * x' ^ 2 - (m' - 4) * x'
  (val / 2).toNat

def check (n j k : ℕ) : Bool :=
  Id.run do
    let bound : ℕ := n + 1
    for z_idx in [0 : 2 * bound + 1] do
      let z : ℤ := (z_idx : ℤ) - (bound : ℤ)
      for x in [0 : n + 2] do
        for y in [0 : n + 2] do
          if G7 z + P j x + P k y == n then
            return true
    return false

def check_3_34 : IO Unit := do
  for n in [0 : 50] do
    if not (check n 3 34) then
      IO.println s!"Failed: (3, 34) at {n}"
      return
  IO.println "All passed."

#eval check_3_34
