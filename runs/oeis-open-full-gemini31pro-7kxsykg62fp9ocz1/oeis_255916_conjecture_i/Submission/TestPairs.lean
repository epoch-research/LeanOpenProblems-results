import Submission.Spec

def check_one (n j k : ℕ) : Bool :=
  let bound := n + 1
  Id.run do
    for z_idx in [0 : 2 * bound + 1] do
      let z : ℤ := (z_idx : ℤ) - (bound : ℤ)
      for x in [0 : bound] do
        for y in [0 : bound] do
          let g := ((5 * z^2 - 3 * z) / 2).toNat
          let p1 := ((j : ℤ) - 2) * x^2 - ((j : ℤ) - 4) * x
          let p2 := ((k : ℤ) - 2) * y^2 - ((k : ℤ) - 4) * y
          if g + (p1 / 2).toNat + (p2 / 2).toNat == n then
            return true
    return false

def check_all_n (j k max_n : ℕ) : Bool :=
  Id.run do
    for n in [0 : max_n] do
      if not (check_one n j k) then
        return false
    return true

def run_tests : IO Unit := do
  let pairs := sun_polygonal_pairs_set.toList
  for p in pairs do
    if not (check_all_n p.1 p.2 50) then
      IO.println s!"Failed pair {p}"
      return
  IO.println "All passed."

#eval run_tests
