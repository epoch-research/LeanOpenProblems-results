import Submission.Spec

def check_conj (p : ℕ) : Bool :=
  (a p) % (p ^ 5) == (a 1) % (p ^ 5)

#eval check_conj 3
#eval check_conj 5
#eval check_conj 7
#eval check_conj 11
