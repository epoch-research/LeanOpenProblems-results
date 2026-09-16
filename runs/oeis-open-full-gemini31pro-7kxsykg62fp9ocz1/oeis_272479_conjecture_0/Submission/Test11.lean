import Mathlib

open Nat

@[simp]
def ninesAsc (M : ℕ) (k : ℕ) : List ℕ :=
  match k with
  | 0 => []
  | k' + 1 => ninesAsc M k' ++ List.replicate 9 (M + k')

def makeListAsc (m M k : ℕ) : List ℕ :=
  [M] ++ ninesAsc M k ++ List.replicate (m - 1) (M + k)

lemma mem_ninesAsc (M k x : ℕ) : x ∈ ninesAsc M k ↔ M ≤ x ∧ x < M + k := by
  induction k with
  | zero => simp
  | succ k' ih =>
    unfold ninesAsc
    simp [ih]
    constructor
    · rintro (⟨h1, h2⟩ | h3)
      · exact ⟨h1, by omega⟩
      · exact ⟨by omega, by omega⟩
    · rintro ⟨h1, h2⟩
      have h3 : x < M + k' ∨ x = M + k' := by omega
      rcases h3 with h3 | h3
      · exact Or.inl ⟨h1, h3⟩
      · exact Or.inr h3

lemma pairwise_le_replicate (n x : ℕ) : (List.replicate n x).Pairwise (· ≤ ·) := by
  apply List.pairwise_replicate.mpr
  exact Or.inr (le_refl _)

lemma pairwise_le_ninesAsc (M k : ℕ) : (ninesAsc M k).Pairwise (· ≤ ·) := by
  induction k with
  | zero => simp
  | succ k' ih =>
    unfold ninesAsc
    apply List.pairwise_append.mpr
    refine ⟨ih, pairwise_le_replicate _ _, ?_⟩
    intro x hx y hy
    rw [mem_ninesAsc] at hx
    have hy2 : y = M + k' := List.eq_of_mem_replicate hy
    omega

lemma pairwise_le_makeListAsc (m M k : ℕ) : (makeListAsc m M k).Pairwise (· ≤ ·) := by
  unfold makeListAsc
  apply List.pairwise_append.mpr
  refine ⟨?_, pairwise_le_replicate _ _, ?_⟩
  · apply List.pairwise_append.mpr
    refine ⟨by simp, pairwise_le_ninesAsc M k, ?_⟩
    intro x hx y hy
    have hx2 : x = M := by simp at hx; exact hx
    rw [mem_ninesAsc] at hy
    omega
  · intro x hx y hy
    have hy2 : y = M + k := List.eq_of_mem_replicate hy
    simp at hx
    rcases hx with hx | hx
    · omega
    · rw [mem_ninesAsc] at hx
      omega
