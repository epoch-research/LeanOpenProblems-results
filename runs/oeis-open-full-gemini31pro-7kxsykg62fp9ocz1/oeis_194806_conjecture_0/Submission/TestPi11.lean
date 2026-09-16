import Mathlib

open Nat Finset

lemma max_div_exists (m K : ℕ) (h : 1 ≤ K) : ∃ d, d ∣ m ∧ d ≤ K ∧ ∀ x, x ∣ m → x ≤ K → x ≤ d := by
  let S := (filter (fun x => x ∣ m) (Icc 1 K))
  have hS : S.Nonempty := by
    use 1
    simp [S, h]
  use S.max' hS
  have h_mem : S.max' hS ∈ S := max'_mem S hS
  simp only [S, mem_filter, mem_Icc] at h_mem
  refine ⟨h_mem.2, h_mem.1.2, ?_⟩
  intro x hx1 hx2
  by_cases hx0 : x = 0
  · subst hx0; exact Nat.zero_le _
  · have hx_mem : x ∈ S := by
      simp only [S, mem_filter, mem_Icc]
      refine ⟨⟨Nat.pos_of_ne_zero hx0, hx2⟩, hx1⟩
    exact le_max' S x hx_mem
