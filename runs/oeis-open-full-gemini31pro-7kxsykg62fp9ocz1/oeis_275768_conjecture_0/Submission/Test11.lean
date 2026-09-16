import Submission.Spec

def all_a : List (ℕ × ℕ) :=
  (List.range 500).map (fun n => (n, a n))

#eval all_a.filter (fun p => p.2 == 4)
