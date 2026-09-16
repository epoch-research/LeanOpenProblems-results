import Mathlib

def check3 (n : ℕ) : Bool :=
  let limit := 3 * n + 4
  let valid_ks := (List.range limit).filter fun k =>
    0 < k ∧ (if k ≤ 3 then true else (k - 3)^2 < 9 * n)
  valid_ks.any fun k => Nat.Prime (Nat.primeCounting (k * n))

#eval (List.range 200).all fun n => if n == 0 then true else check3 n
