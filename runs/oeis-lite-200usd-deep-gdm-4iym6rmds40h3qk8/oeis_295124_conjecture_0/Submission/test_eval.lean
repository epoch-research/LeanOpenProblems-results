import Submission.Spec

def find_true (a b : ℕ) : List ℕ :=
  if b < a then []
  else if verify_candidate a then
    a :: find_true (a + 1) b
  else
    find_true (a + 1) b

#eval find_true 23206 100000
