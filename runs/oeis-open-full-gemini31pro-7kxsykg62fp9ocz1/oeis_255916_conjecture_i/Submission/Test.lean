import Submission.Spec

def G7 (k : ℤ) : ℕ := ((5 * k^2 - 3 * k) / 2).toNat
def P (m : ℕ) (x : ℕ) : ℕ := ((m - 2) * x^2 - (m - 4) * x) / 2

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

#eval! check 51 3 20
