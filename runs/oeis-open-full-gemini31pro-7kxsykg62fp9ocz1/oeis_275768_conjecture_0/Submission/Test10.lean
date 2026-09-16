import Submission.Spec

def find_4 : List ℕ :=
  (List.range 500).filter (fun n => a n == 4)

#eval find_4
