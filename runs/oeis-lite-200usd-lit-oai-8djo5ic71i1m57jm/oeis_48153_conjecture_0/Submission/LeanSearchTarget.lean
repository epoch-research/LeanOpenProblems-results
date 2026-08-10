import FormalConjectures.Util.ProblemImports
#find (∀ n : ℕ, Finset.sum (Finset.range n) (fun k => k ^ 2 % n) ≤ _)
#find (Finset.sum (Finset.range ?n) (fun k => k ^ 2 % ?n) ≤ (?n ^ 2 - 1) / 2)
#find (Finset.sum (Finset.range ?n) (fun k => k ^ 2 % ?n) ≤ ?n * (?n - 1) / 2)
