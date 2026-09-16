import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0

def M : ℕ := 1194649

def dc_mod (fuel a b : ℕ) : ℕ × ℤ :=
  match fuel with
  | 0 => (1, 0)
  | fuel' + 1 =>
    if b ≤ a then (1, 0)
    else if b = a + 1 then (a % M, if a % 2 = 0 then 1 else -1)
    else
      let m := (a + b) / 2
      let (p1, f1) := dc_mod fuel' a m
      let (p2, f2) := dc_mod fuel' m b
      ((p1 * p2) % M, (f1 * (p2 : ℤ) + (p1 : ℤ) * f2) % (M : ℤ))

theorem test : (dc_mod 20 2 200000).2 = 0 := by decide
