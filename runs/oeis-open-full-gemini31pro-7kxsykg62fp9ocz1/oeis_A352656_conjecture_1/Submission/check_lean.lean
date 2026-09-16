import Submission.Spec
def check (p r a b c : ℕ) : Bool :=
  let lhs := F (a * p ^ r) (b * p ^ r) (c * p ^ r)
  let rhs := F (a * p ^ (r - 1)) (b * p ^ (r - 1)) (c * p ^ (r - 1))
  (lhs % (p ^ (4 * r))) == ((rhs ^ p) % (p ^ (4 * r)))

#eval check 2 2 3 3 3
