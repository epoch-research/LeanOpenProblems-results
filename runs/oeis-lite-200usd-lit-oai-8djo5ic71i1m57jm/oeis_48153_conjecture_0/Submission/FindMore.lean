import FormalConjectures.Util.ProblemImports
open Finset
#find (∑ k ∈ Finset.range ?n, k ^ 2 % ?n ≤ ?n * (?n - 1) / 2)
#find (∑ k ∈ Finset.range ?n, k ^ 2 % ?n ≤ (?n ^ 2 - 1) / 2)
#find (∑ k ∈ Finset.range ?n, k ^ 2 / ?n ≥ _)
#find (_ ≤ ∑ k ∈ Finset.range ?n, k ^ 2 / ?n)
#find (∑ k ∈ Finset.range ?n, (k ^ 2 : ℕ) % ?n = _)
#find (∑ k ∈ Finset.range ?n, (k ^ 2 : ℤ) % ?n = _)
