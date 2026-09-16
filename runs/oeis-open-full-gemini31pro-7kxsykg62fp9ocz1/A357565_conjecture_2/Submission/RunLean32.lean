import Submission.Spec
open Finset Nat

def mod_val : ℕ := 79 ^ 9
def a79_2 : ℕ := A357565 (79 ^ 2)
def a79_1 : ℕ := A357565 79

#eval a79_2 % mod_val == a79_1 % mod_val
