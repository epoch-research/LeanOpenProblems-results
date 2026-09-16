import Submission.Spec

def evalA : List (ℕ × ℕ) :=
  (List.range 200).map (fun n => (n, a n))

#eval evalA.filter (fun p => p.2 == 4)
