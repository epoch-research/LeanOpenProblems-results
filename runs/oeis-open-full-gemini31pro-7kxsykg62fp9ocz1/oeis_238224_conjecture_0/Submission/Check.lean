import Submission.Spec

def checkA (n : ℕ) : ℕ :=
  Id.run <| do
    let mut sum := 0
    for j in [1:n] do
      let upper_q := (n - 1) / j
      for q in [1:upper_q+1] do
        let k := j * q + 1
        if (Nat.primeCounting (j * n) > 0) && (Nat.primeCounting (k * n) % Nat.primeCounting (j * n) == 0) then
          sum := sum + 1
    return sum

#eval checkA 2
#eval checkA 21
