import Submission.Spec
open Int

def test_conj (p k : ℕ) : Bool :=
  (A361711 (p ^ k) - A361711 (p ^ (k - 1))) % (p ^ (3 * k) : ℤ) == 0

#eval test_conj 5 1
#eval test_conj 5 2
#eval test_conj 7 1
#eval test_conj 11 1
#eval test_conj 13 1
