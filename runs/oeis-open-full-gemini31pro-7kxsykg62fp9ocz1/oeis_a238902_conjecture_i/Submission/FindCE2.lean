import Submission.Spec

def check_n (n : ℕ) : Bool :=
  a n == 0

def find_ce (start : ℕ) (limit : ℕ) : Option ℕ :=
  (List.range limit).find? fun i =>
    let n := start + i
    if n > 0 then check_n n else false

def main : IO Unit := do
  IO.println (find_ce 1 500)
