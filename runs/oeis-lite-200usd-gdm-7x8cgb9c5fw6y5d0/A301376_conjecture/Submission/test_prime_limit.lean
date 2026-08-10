import FormalConjectures.Util.ProblemImports
open List

lemma prime_3 : Nat.Prime 3 := by norm_num
lemma prime_11 : Nat.Prime 11 := by norm_num
lemma prime_31 : Nat.Prime 31 := by norm_num
lemma prime_83 : Nat.Prime 83 := by norm_num

lemma prime_of_mem {p : ℕ} (h : p ∈ [3, 11, 31, 83]) : Nat.Prime p := by
  simp only [mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_11
  · exact prime_31
  · exact prime_83
  · cases h_false
