import FormalConjectures.Util.ProblemImports
open Finset

def A048153 (n : ℕ) : ℕ := Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

example (n : ℕ) (h : 1 ≤ n) : A048153 n ≤ (n ^ 2 - 1) / 2 := by
  unfold A048153
  apply?

example (m : ℕ) : (∑ k in Finset.Icc 1 m, (k^2 % (2*m+1))) ≤ (2*m+1)*m/2 := by
  apply?

example (m : ℕ) : (∑ k in Finset.Icc 1 m, (k^2 / (2*m+1))) ≥ (m*(m-2))/6 := by
  apply?
