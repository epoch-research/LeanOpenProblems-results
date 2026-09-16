import Submission.Spec
open Finset

def S2 : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  let P1 (z : ℕ) : ℕ := (z * (3 * z - 1)) / 2
  let P2 (w : ℕ) : ℕ := (w * (3 * w + 1)) / 2
  let B : Finset ℕ := range 3
  (B.product B).product (B.product B)
    |>.filter (fun p =>
      let x := p.fst.fst
      let y := p.fst.snd
      let z := p.snd.fst
      let w := p.snd.snd
      x^5 + 2 * y^5 + P1 z + P2 w = 2
    )

#eval S2
