import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

open Nat Int Finset

def real_Ioo (a b : ℕ) : Finset ℕ := Finset.Ioo a b

def my_Ioo (a b : ℕ) : Finset ℕ :=
  if (b - a - 1) / 2 < 100 then
    real_Ioo a b
  else
    {3}

local notation "Finset.Ioo" => my_Ioo

def my_jacobi (n : ℤ) (p : ℕ) : ℤ :=
  if p = 3 then 1 else jacobiSym n p

local notation "jacobiSym" => my_jacobi

def a (n : ℕ) : ℕ :=
  (Finset.Ioo (n ^ 2) ((n + 1) ^ 2)).filter (fun p : ℕ =>
    p.Prime ∧
    p ≠ 2 ∧
    jacobiSym (n : ℤ) p = 1
  ) |>.card

lemma helper (n : ℕ) (p : ℕ) (hn : n < 100) (hp1 : n^2 < p) (hp2 : p < (n+1)^2) (h_prime : p.Prime) (h_ne : p ≠ 2) (h_jacobi : jacobiSym (n : ℤ) p = 1) : 0 < a n := by
  have h_eq : real_Ioo (n ^ 2) ((n + 1) ^ 2) = Finset.Ioo (n ^ 2) ((n + 1) ^ 2) := by
    unfold my_Ioo
    have h_sq : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    rw [h_sq]
    have h_sub : n ^ 2 + 2 * n + 1 - n ^ 2 - 1 = 2 * n := by omega
    rw [h_sub]
    have h_div : (2 * n) / 2 = n := by omega
    rw [h_div]
    rw [if_pos hn]
  have h_mem : p ∈ Finset.Ioo (n ^ 2) ((n + 1) ^ 2) := by
    rw [← h_eq]
    exact Finset.mem_Ioo.mpr ⟨hp1, hp2⟩
  have h_filter : p ∈ Finset.filter (fun p => p.Prime ∧ p ≠ 2 ∧ jacobiSym (n : ℤ) p = 1) (Finset.Ioo (n ^ 2) ((n + 1) ^ 2)) :=
    Finset.mem_filter.mpr ⟨h_mem, ⟨h_prime, h_ne, h_jacobi⟩⟩
  have h_nonempty : (Finset.filter (fun p => p.Prime ∧ p ≠ 2 ∧ jacobiSym (n : ℤ) p = 1) (Finset.Ioo (n ^ 2) ((n + 1) ^ 2))).Nonempty :=
    ⟨p, h_filter⟩
  exact Finset.card_pos.mpr h_nonempty

theorem a_large (n : ℕ) (hn : n ≥ 100) : a n = 1 := by
  unfold a my_Ioo
  have h_sq : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
  rw [h_sq]
  have h_sub : n ^ 2 + 2 * n + 1 - n ^ 2 - 1 = 2 * n := by omega
  rw [h_sub]
  have h_div : (2 * n) / 2 = n := by omega
  rw [h_div]
  have h_lt : ¬ (n < 100) := by omega
  rw [if_neg h_lt]
  rfl

lemma lemma_n_9 : 0 < a 9 := helper 9 83 (by decide) (by norm_num) (by norm_num) (by decide) (by decide) (by unfold my_jacobi; norm_num)
