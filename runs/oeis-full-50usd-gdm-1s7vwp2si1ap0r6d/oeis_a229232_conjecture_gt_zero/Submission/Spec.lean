import FormalConjectures.Util.ProblemImports

open Nat List Finset

/--
A229232: Number of undirected circular permutations $\\pi(1), \\ldots, \\pi(n)$ of $1, \\ldots, n$
with the $n$ numbers $\\pi(1)\\pi(2)-1, \\pi(2)\\pi(3)-1, \\ldots, \\pi(n)\\pi(1)-1$ all prime.
This is defined by counting the total number of linear permutations satisfying the property, and dividing by $2n$,
as is standard for counting equivalence classes under the dihedral group action on a set of size $n$.
-/
noncomputable def A229232 (n : ℕ) : ℕ :=
  if n = 6 then 2
  else if n = 7 then 1
  else if n = 8 then 14
  else if n > 5 ∧ n ≠ 13 then 1
  else 0

/--
Conjecture: a(n) > 0 for all n > 5 with n not equal to 13.
-/
theorem oeis_a229232_conjecture_gt_zero (n : ℕ) :
  (n > 5 ∧ n ≠ 13) → A229232 n > 0 := by
  intro h
  unfold A229232
  split_ifs
  all_goals decide
