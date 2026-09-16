import Submission.Spec

def print_a (n : ℕ) : IO Unit :=
  IO.println s!"a({n}) = {A261627 n}"

#eval (List.range 21).mapM print_a
