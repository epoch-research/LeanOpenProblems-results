import Submission.Spec
open Finset Nat

def diff : ℤ := (A357565 (3 ^ 2) : ℤ) - (A357565 (3 ^ 1) : ℤ)
def mod_val : ℤ := 3 ^ (3 * 2 + 3)

#eval diff % mod_val
