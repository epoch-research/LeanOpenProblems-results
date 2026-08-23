import FormalConjectures.Util.ProblemImports

open Nat Finset

def Sset (n : ℕ) : Finset ℕ :=
  Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n)

lemma mem_Sset_iff {n q : ℕ} :
    q ∈ Sset n ↔ q < n ∧ q.Prime ∧ (n - q).Prime ∧ (n + q).Prime := by
  simp [Sset, mem_filter, mem_range]

set_option maxHeartbeats 0

example : 5 ∈ Sset 24 := by
  rw [mem_Sset_iff]; refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

example : 109 ∈ Sset 288 := by
  rw [mem_Sset_iff]; refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

example : 181 ∈ Sset 192 := by
  rw [mem_Sset_iff]; refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

example : 7 ∈ Sset 204 := by
  rw [mem_Sset_iff]; refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num
