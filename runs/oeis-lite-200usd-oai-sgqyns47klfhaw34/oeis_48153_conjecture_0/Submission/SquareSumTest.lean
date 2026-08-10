import FormalConjectures.Util.ProblemImports
open Finset

lemma sum_range_sq_formula_succ (n : ℕ) :
    6 * (Finset.sum (Finset.range (n+1)) (fun i => i ^ 2)) = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [Nat.mul_add]
      rw [ih]
      ring_nf

lemma sum_range_sq_formula (n : ℕ) :
    6 * (Finset.sum (Finset.range n) (fun i => i ^ 2)) = n * (n - 1) * (2 * n - 1) := by
  cases n with
  | zero => simp
  | succ n =>
      rw [sum_range_sq_formula_succ]
      have h : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
      rw [h]
      have h2 : n + 1 - 1 = n := by omega
      rw [h2]
      ring_nf

#check sum_range_sq_formula
