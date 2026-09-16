import Submission.Spec

def find_4 (max_n : ℕ) : List ℕ :=
  (List.range max_n).filter (fun n => a n == 4)

#eval find_4 300
