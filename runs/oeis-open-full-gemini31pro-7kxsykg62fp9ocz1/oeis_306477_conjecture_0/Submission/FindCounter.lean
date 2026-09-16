import Submission.Spec

def find_counterexample (n : ℕ) : Option ℕ :=
  if n = 0 then none
  else
    let res := Id.run <| do
      for i in [1:n+1] do
        if A306477 i == 0 then
          return some i
      return none
    res

#eval find_counterexample 100
