import FormalConjectures.Util.ProblemImports
open Nat

lemma test_sup (n : ℕ) (f : ℕ → ℕ) : ∃ k ≤ n, (Finset.range (n + 1)).sup f = f k := by
  have h : (Finset.range (n + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (succ_pos n)⟩
  rcases Finset.exists_mem_eq_sup _ h f with ⟨k, hk, hM⟩
  exact ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), hM⟩
