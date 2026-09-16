import Submission.Spec
def check_congruence (p k n : ℕ) : Bool :=
  let val1 := a (n * p ^ k)
  let val2 := a (n * p ^ (k - 1))
  let mod := p ^ (3 * k)
  (val1 % mod) == (val2 % mod)

#eval check_congruence 5 2 1
