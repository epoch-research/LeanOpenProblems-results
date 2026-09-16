import Submission.Spec
open Polynomial Rat Finset Nat

def comp_bernoulli : ℕ → ℚ
| 0 => 1
| n + 1 => - (∑ k ∈ range (n + 1), (comp_bernoulli k) * (choose (n + 2) k) : ℚ) / (n + 2)
termination_by n => n
decreasing_by
  simp_wf
  omega

def comp_poly_bernoulli (n : ℕ) : ℚ[X] :=
  ∑ i ∈ range (n + 1), Polynomial.monomial (n - i) (comp_bernoulli i * choose n i)

def comp_A195441 (n : ℕ) : ℕ :=
  let N := n + 1
  let B_num : ℚ := comp_bernoulli N
  let P : ℚ[X] := comp_poly_bernoulli N - C B_num
  (range (N + 1)).fold (fun a b => Nat.lcm a b) 1 fun k => (P.coeff k).den

-- We need a computable radical
def comp_radical (n : ℕ) : ℕ :=
  if n = 0 then 1
  else if n = 1 then 1
  else
    let facs := (List.range (n + 1)).filter (fun p => p.Prime ∧ p ∣ n)
    facs.foldl (· * ·) 1

#eval comp_A195441 7
#eval comp_radical 9
