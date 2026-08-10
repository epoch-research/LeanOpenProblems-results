import FormalConjectures.Util.ProblemImports

open Nat Finset

def A352965 : ℕ → ℕ
| 0 => 0
| 1 => 0
| n + 1 =>
  let k := n
  let a_k := A352965 k
  let all_lt_k := Finset.range k
  let S := all_lt_k.filter (fun p =>
    Nat.Prime p ∧ A352965 (k - p) = a_k)
  if h : S.Nonempty then
    S.min' h
  else
    0

lemma not_appears_imp (p : ℕ) (hp : Nat.Prime p) (h_not : ∀ n, A352965 n ≠ p) :
    ∀ n, p < n → A352965 n = A352965 (n - p) → ∃ q < p, Nat.Prime q ∧ A352965 n = A352965 (n - q) := by
  intro n hp_lt heq
  rcases n with _ | n
  · exfalso; omega
  -- Now n is n.succ, so n + 1 = n.succ.succ
  have h_not_succ := h_not (n + 1 + 1)
  -- A352965 (n + 1 + 1)
  -- Let's define S on (n+1)
  let S := (Finset.range (n + 1)).filter (fun r => Nat.Prime r ∧ A352965 (n + 1 - r) = A352965 (n + 1))
  have hS_nonempty : S.Nonempty := by
    have h1 : p ∈ Finset.range (n + 1) := by
      rw [Finset.mem_range]
      omega
    have h2 : Nat.Prime p ∧ A352965 (n + 1 - p) = A352965 (n + 1) := by
      refine ⟨hp, ?_⟩
      have : n + 1 - p = n.succ - p := rfl
      rw [heq]
    have h_mem : p ∈ S := by
      rw [Finset.mem_filter]
      exact ⟨h1, h2⟩
    exact ⟨p, h_mem⟩
  have h_eq_min : A352965 (n + 1 + 1) = S.min' hS_nonempty := by
    unfold A352965
    simp only [S]
    split_ifs with h_ne
    · rfl
    · exfalso; exact h_ne hS_nonempty
  rw [h_eq_min] at h_not_succ
  let q := S.min' hS_nonempty
  have hq_mem : q ∈ S := Finset.min'_mem S hS_nonempty
  have hp_mem : p ∈ S := by
    rw [Finset.mem_filter]
    refine ⟨by rw [Finset.mem_range]; omega, hp, ?_⟩
    rw [heq]
  have hq_le : q ≤ p := Finset.min'_le S p hp_mem
  have hq_ne : q ≠ p := by
    intro h_eq
    subst h_eq
    exact h_not_succ rfl
  have hq_lt : q < p := lt_of_le_of_ne hq_le hq_ne
  have hq_mem' : q ∈ (Finset.range (n + 1)).filter (fun r => Nat.Prime r ∧ A352965 (n + 1 - r) = A352965 (n + 1)) := hq_mem
  rw [Finset.mem_filter] at hq_mem'
  use q
  refine ⟨hq_lt, hq_mem'.2.1, hq_mem'.2.2.symm⟩


#print axioms not_appears_imp
