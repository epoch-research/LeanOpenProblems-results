import Submission.Spec

def listA : List (ℕ × ℕ) :=
  (List.range 24).map (fun n => (n, a n))

#eval listA
