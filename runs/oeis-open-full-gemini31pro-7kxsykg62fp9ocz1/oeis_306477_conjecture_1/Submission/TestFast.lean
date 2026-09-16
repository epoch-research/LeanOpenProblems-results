import Submission.Spec

def check_all : ℕ → Bool
| 0 => true
| n + 1 => (A306477 (n + 1) > 0) && check_all n

#eval check_all 20
