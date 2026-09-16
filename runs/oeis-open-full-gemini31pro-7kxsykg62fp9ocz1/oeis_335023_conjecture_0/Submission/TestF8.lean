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
  have H1 : Ico 1 (n + 1) = {1} ∪ Ico 2 (n + 1) := by
    ext x
    simp only [mem_Ico, mem_union, mem_singleton]
    omega
  have hd : Disjoint ({1} : Finset ℕ) (Ico 2 (n + 1)) := by
    simp [disjoint_singleton_left, mem_Ico]
  have H2 : ∏ j ∈ Ico 1 (n + 1), j = n.factorial := prod_Ico_id_eq_factorial n
  rw [H1, prod_union hd, prod_singleton, one_mul] at H2
  exact H2.symm

lemma n_fact_div_eq (n k : ℕ) (hn : 2 ≤ n) (hk : k ∈ Ico 2 (n + 1)) :
  (n.factorial : ℤ) / (k : ℤ) = ∏ j ∈ (Ico 2 (n + 1)).erase k, (j : ℤ) := by
  have H_prod : ∏ j ∈ Ico 2 (n + 1), (j : ℤ) = (k : ℤ) * ∏ j ∈ (Ico 2 (n + 1)).erase k, (j : ℤ) := by
    have := mul_prod_erase (Ico 2 (n + 1)) (fun x => (x : ℤ)) hk
    exact this.symm
  have H_fact : (n.factorial : ℤ) = ∏ j ∈ Ico 2 (n + 1), (j : ℤ) := by
    rw [n_fact_eq_prod n hn]
    push_cast
    rfl
  rw [H_fact, H_prod]
  have hk_nz : (k : ℤ) ≠ 0 := by
    simp only [mem_Ico] at hk
    omega
  exact Int.mul_ediv_cancel_left _ hk_nz

lemma F_aux_eq_S_def (n : ℕ) (hn : 2 ≤ n) : F_aux n = S_def 2 (n + 1) := by
  dsimp [F_aux, S_def]
  rw [if_neg (by omega)]
  have h_ico : Icc 2 n = Ico 2 (n + 1) := by
    ext x
    rw [mem_Icc, mem_Ico]
    omega
  rw [h_ico]
  apply sum_congr rfl
  intro k hk
  dsimp [term]
  congr 1
  exact n_fact_div_eq n k hn hk

