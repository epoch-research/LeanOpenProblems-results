import Submission.Spec
open Nat Finset

def check_n (n : ℕ) : Bool :=
  A352628 n > 0

#eval check_n 0
#eval check_n 1
#eval check_n 2
#eval check_n 3
#eval check_n 4
#eval check_n 5
#eval check_n 6
#eval check_n 7
#eval check_n 14
#eval check_n 62
