import FormalConjectures.Util.ProblemImports
open Finset

lemma prefix_strong (N j : ℕ) (h : 2*j < N) :
    (∑ i ∈ Finset.Icc 1 j, (i^2 % N)) ≤ j*(N-j) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hj : 2*j < N := by omega
      have ih' := ih hj
      have hmod : (j+1)^2 % N ≤ N := by exact Nat.mod_le _ _
      nlinarith [ih', hmod]
