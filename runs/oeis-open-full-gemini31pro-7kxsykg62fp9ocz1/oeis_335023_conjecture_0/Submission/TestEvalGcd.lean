import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 2000000

def dc_fuel (fuel a b : ℕ) : ℕ × ℤ :=
  match fuel with
  | 0 => (1, 0)
  | fuel' + 1 =>
    if b ≤ a then (1, 0)
    else if b = a + 1 then (a, if a % 2 = 0 then (1 : ℤ) else -1)
    else
      let m := (a + b) / 2
      let (p1, f1) := dc_fuel fuel' a m
      let (p2, f2) := dc_fuel fuel' m b
      (p1 * p2, f1 * (p2 : ℤ) + (p1 : ℤ) * f2)

#eval Int.gcd (dc_fuel 21 2 1194650).2 (dc_fuel 21 2 1194649).2 > 0
