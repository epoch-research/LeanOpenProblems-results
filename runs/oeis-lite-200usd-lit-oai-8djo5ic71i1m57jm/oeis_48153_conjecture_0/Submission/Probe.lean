import FormalConjectures.Util.ProblemImports

open Finset

def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

#find (Finset.sum (Finset.range ?n) (fun k => k ^ 2 % ?n) ≤ _)
#find (_ ≤ (Finset.sum (Finset.range ?n) (fun k => k ^ 2 % ?n)))
#find (∑ k ∈ Finset.range ?n, k ^ 2 % ?n ≤ _)
#find (∑ k in Finset.range ?n, k ^ 2 % ?n ≤ _)
#find (_ ^ 2 % _ ≤ _)

example (n : ℕ) (h : 1 ≤ n) : A048153 n ≤ (n ^ 2 - 1) / 2 := by
  unfold A048153
  exact?
