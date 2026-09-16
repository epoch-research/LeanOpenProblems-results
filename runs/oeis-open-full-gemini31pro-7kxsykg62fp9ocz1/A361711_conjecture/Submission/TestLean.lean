import Submission.Spec
open Int

def test2 : Bool :=
  let p := 5
  let k := 2
  let lhs := A361711 (p ^ k)
  let rhs := A361711 (p ^ (k - 1))
  let n := (p ^ (3 * k) : ℕ)
  lhs % n == rhs % n

#eval test2
