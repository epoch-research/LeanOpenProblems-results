import FormalConjectures.Util.ProblemImports

open Nat Int Finset

def F_aux (n : ℕ) : ℤ :=
  if n < 2 then 0 else
  Finset.sum (Icc 2 n) $ fun k : ℕ =>
    let n_fact : ℤ := n.factorial
    let k_int : ℤ := k
    let quotient : ℤ := n_fact / k_int
    quotient * (if k % 2 = 0 then 1 else -1)

theorem F_aux_rec (n : ℕ) (hn : n ≥ 2) :
  F_aux (n + 1) = (n + 1 : ℤ) * F_aux n + (if (n + 1) % 2 = 0 then 1 else -1) * (n.factorial : ℤ) := by
  sorry

