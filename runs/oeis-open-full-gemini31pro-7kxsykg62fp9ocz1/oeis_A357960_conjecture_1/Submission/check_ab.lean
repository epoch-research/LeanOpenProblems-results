import Submission.Spec
open Nat

def B (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum fun k => (n.choose k) ^ 2 * ((n + k).choose k)

def A (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum fun k => (n.choose k) ^ 2 * ((n + k).choose k) ^ 2

#eval B 1
#eval A 0
#eval a 1

#eval B 3
#eval A 2
#eval a 3

#eval (a 3) % (3^5)
#eval (a 1) % (3^5)
