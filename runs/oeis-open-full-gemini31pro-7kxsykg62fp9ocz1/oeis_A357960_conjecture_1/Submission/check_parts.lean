import Submission.Spec
open Nat Finset

def A_part (n : ℕ) :=
  let N := n - 1
  (range n).sum fun k => (N.choose k) ^ 2 * ((N + k).choose k) ^ 2

def B_part (n : ℕ) :=
  (range (n + 1)).sum fun k => (n.choose k) ^ 2 * ((n + k).choose k)

#eval A_part 1
#eval B_part 1
