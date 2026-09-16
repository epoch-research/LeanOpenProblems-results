import Submission.Spec

def findCounterexample : Option ℕ :=
  (List.range 100).find? fun n =>
    if n > 0 then a n == 0 else false

#eval findCounterexample
