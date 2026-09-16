import Submission.Spec

def check_all : List ℕ :=
  (List.range 106).filter (fun n => A352286 n == 0)

#eval check_all
