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

def pairs : List (ℕ × ℕ) := [
  (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10),
  (3, 11), (3, 12), (3, 13), (3, 14), (3, 15), (3, 16), (3, 17), (3, 18), (3, 19),
  (3, 21), (3, 22), (3, 23), (3, 24), (3, 26), (3, 27), (3, 29), (3, 30),
  (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11),
  (4, 13), (4, 14), (4, 17), (4, 19), (4, 20), (4, 23), (4, 26),
  (5, 6), (5, 9), (6, 7), (8, 9)
]

def check_all : IO Unit := do
  for p in pairs do
    for n in [0 : 50] do
      if not (check n p.1 p.2) then
        IO.println s!"Failed: pair {p} at {n}"
        return
  IO.println "All passed."

#eval check_all
