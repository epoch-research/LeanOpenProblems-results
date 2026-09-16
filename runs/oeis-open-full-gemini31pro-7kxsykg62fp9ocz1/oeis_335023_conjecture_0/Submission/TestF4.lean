import FormalConjectures.Util.ProblemImports

open Nat Int Finset

def F_aux (n : ℕ) : ℤ :=
  if n < 2 then 0 else
  Finset.sum (Icc 2 n) $ fun k : ℕ =>
    let n_fact : ℤ := n.factorial
    let k_int : ℤ := k
    let quotient : ℤ := n_fact / k_int
    quotient * (if k % 2 = 0 then 1 else -1)

def P_def (a b : ℕ) : ℕ := ∏ k ∈ Ico a b, k

def term (a b k : ℕ) : ℤ :=
  (∏ j ∈ (Ico a b).erase k, (j : ℤ)) * (if k % 2 = 0 then 1 else -1)

def S_def (a b : ℕ) : ℤ :=
  ∑ k ∈ Ico a b, term a b k

lemma n_fact_eq_prod (n : ℕ) (hn : 2 ≤ n) : n.factorial = ∏ j ∈ Ico 2 (n + 1), j := by
  have H1 : Icc 1 n = {1} ∪ Ico 2 (n + 1) := by
    ext x
    simp only [mem_Icc, mem_union, mem_singleton, mem_Ico]
    omega
  have hd : Disjoint ({1} : Finset ℕ) (Ico 2 (n + 1)) := by
    simp [disjoint_singleton_left, mem_Ico]
  have H2 : ∏ j ∈ Icc 1 n, j = ∏ j ∈ {1} ∪ Ico 2 (n + 1), j := by rw [H1]
  rw [prod_union hd, prod_singleton, one_mul] at H2
  have H3 : n.factorial = ∏ j ∈ Icc 1 n, j := by
    sorry
  rw [H3, H2]

