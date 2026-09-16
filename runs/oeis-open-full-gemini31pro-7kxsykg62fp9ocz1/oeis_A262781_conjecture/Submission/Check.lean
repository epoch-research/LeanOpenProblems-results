import Submission.Spec
open Nat

def A262781_tuples (n : ℕ) : List (ℕ × ℕ × ℕ) :=
  let R_x := Finset.range (Nat.sqrt n + 1)
  let R_y_z := (Finset.range (n + 1)).product (Finset.range (n + 1))

  ((R_x.product R_y_z)
  |>.filter (fun p =>
    let x := p.fst
    let y := p.snd.fst
    let z := p.snd.snd

    0 < y ∧ y ≤ z ∧
    (y.Prime ∨ z.Prime) ∧
    x^2 + totient (y ^ 2) + totient (z ^ 2) = n
  )).toList |>.map (fun p => (p.fst, p.snd.fst, p.snd.snd))

#eval A262781_tuples 36
