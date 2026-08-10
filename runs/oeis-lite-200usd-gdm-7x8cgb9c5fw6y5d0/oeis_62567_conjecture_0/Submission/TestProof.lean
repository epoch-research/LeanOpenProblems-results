import FormalConjectures.Util.ProblemImports

open Nat

theorem list_all_nines (L : List ℕ) (h_len : L.length = 9) (h_sum : L.sum = 81) (h_lt : ∀ x ∈ L, x < 10) :
    L = [9, 9, 9, 9, 9, 9, 9, 9, 9] := by
  rcases L with _ | ⟨d1, _ | ⟨d2, _ | ⟨d3, _ | ⟨d4, _ | ⟨d5, _ | ⟨d6, _ | ⟨d7, _ | ⟨d8, _ | ⟨d9, _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try contradiction
  have h_d1 : d1 < 10 := h_lt d1 (by simp)
  have h_d2 : d2 < 10 := h_lt d2 (by simp)
  have h_d3 : d3 < 10 := h_lt d3 (by simp)
  have h_d4 : d4 < 10 := h_lt d4 (by simp)
  have h_d5 : d5 < 10 := h_lt d5 (by simp)
  have h_d6 : d6 < 10 := h_lt d6 (by simp)
  have h_d7 : d7 < 10 := h_lt d7 (by simp)
  have h_d8 : d8 < 10 := h_lt d8 (by simp)
  have h_d9 : d9 < 10 := h_lt d9 (by simp)
  have h_sum' : d1 + d2 + d3 + d4 + d5 + d6 + d7 + d8 + d9 = 81 := by
    simp [List.sum] at h_sum
    exact h_sum
  have h_eq1 : d1 = 9 := by omega
  have h_eq2 : d2 = 9 := by omega
  have h_eq3 : d3 = 9 := by omega
  have h_eq4 : d4 = 9 := by omega
  have h_eq5 : d5 = 9 := by omega
  have h_eq6 : d6 = 9 := by omega
  have h_eq7 : d7 = 9 := by omega
  have h_eq8 : d8 = 9 := by omega
  have h_eq9 : d9 = 9 := by omega
  subst h_eq1 h_eq2 h_eq3 h_eq4 h_eq5 h_eq6 h_eq7 h_eq8 h_eq9
  rfl
