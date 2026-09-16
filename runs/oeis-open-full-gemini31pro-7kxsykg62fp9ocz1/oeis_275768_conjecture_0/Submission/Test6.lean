import Submission.Spec

def allA : List (ℕ × ℕ) :=
  (List.range 2000).map (fun n => (n, a n))

#eval allA.filter (fun p => p.2 == 4)
