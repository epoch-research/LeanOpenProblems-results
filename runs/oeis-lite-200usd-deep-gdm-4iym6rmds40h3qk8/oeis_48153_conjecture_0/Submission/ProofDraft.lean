import FormalConjectures.Util.ProblemImports

open Finset

def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

lemma sq_sub_mod (n k : ℕ) (h : k ≤ n) : (n - k) ^ 2 % n = k ^ 2 % n := sorry

-- Let's see if we can prove the conjecture for n >= 5 by some other method.
