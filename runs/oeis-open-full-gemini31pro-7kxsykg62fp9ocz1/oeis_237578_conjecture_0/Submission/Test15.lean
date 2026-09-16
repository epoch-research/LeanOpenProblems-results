import Mathlib

def check3 (n : ℕ) : Bool :=
  if n == 0 then true
  else
    let ks := (List.range (3 * n + 3)).filter (fun k =>
      k > 0 ∧ (if k < 3 then true else (k - 3) * (k - 3) < 9 * n))
    ks.any (fun k => Nat.Prime (Nat.primeCounting (k * n)))

#eval (List.range 100).all check3
