import FormalConjectures.Util.ProblemImports

open Nat Int Finset

lemma n_fact_eq_prod (n : ℕ) (hn : 2 ≤ n) : n.factorial = ∏ j ∈ Ico 2 (n + 1), j := by
  have H1 : Ico 1 (n + 1) = {1} ∪ Ico 2 (n + 1) := by
    ext x
    simp only [mem_Ico, mem_union, mem_singleton]
    omega
  have hd : Disjoint ({1} : Finset ℕ) (Ico 2 (n + 1)) := by
    simp [disjoint_singleton_left, mem_Ico]
  have H2 : n.factorial = ∏ j ∈ Ico 1 (n + 1), j := by
    exact eq_comm.mp (Nat.prod_Ico_id_eq_factorial 1 (n + 1))
    -- wait, Nat.prod_Ico_id_eq_factorial doesn't exist?
  sorry
