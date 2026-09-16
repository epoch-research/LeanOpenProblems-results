import Submission.Spec

#check (5, 7) ∈ C_pairs
#check (0, 0) ∈ C_pairs

def check_in (x y : ℕ) : Bool :=
  if (x, y) = (5, 7) ∨ (x, y) = (5, 9) ∨ (x, y) = (5, 13) ∨ (x, y) = (6, 5) ∨ (x, y) = (6, 7) ∨ (x, y) = (7, 5) then true else false

