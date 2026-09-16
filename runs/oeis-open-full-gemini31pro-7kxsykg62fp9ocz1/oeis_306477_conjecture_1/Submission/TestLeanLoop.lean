import Submission.Spec

def check_all : ℕ → ℕ
| 0 => 0
| n + 1 => if A306477 (n + 1) == 0 then n + 1 else check_all n

#eval check_all 200
