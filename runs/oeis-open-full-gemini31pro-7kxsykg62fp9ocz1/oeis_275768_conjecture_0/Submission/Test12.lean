import Submission.Spec

def find_4 : List ℕ :=
  (List.range 5000).filter (fun n => a n == 4)

#eval find_4
