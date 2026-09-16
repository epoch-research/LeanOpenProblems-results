import Submission.Spec
open Rat Finset Nat

def comp_bernoulli : ℕ → ℚ
| 0 => 1
| n + 1 => - (((List.range (n + 1)).map (fun k => (comp_bernoulli k) * (choose (n + 2) k))).foldl (· + ·) 0) / (n + 2)

def comp_coeff (N : ℕ) (k : ℕ) : ℚ :=
  if k == 0 then 0
  else if k <= N then
    comp_bernoulli (N - k) * choose N (N - k)
  else 0

def comp_A195441 (n : ℕ) : ℕ :=
  let N := n + 1
  (List.range (N + 1)).foldl (fun a k => Nat.lcm a (comp_coeff N k).den) 1

#eval! comp_A195441 7
#eval! comp_A195441 1
#eval! comp_A195441 2
