import FormalConjectures.Util.ProblemImports

def check_digits_01 : List Nat -> Bool
  | [] => true
  | d :: ds => (d == 0 || d == 1) && check_digits_01 ds

theorem check_digits_01_ok : ∀ (l : List Nat), check_digits_01 l = true -> ∀ d ∈ l, d = 0 ∨ d = 1
  | [], _ => by intro d hd; contradiction
  | d' :: ds, h => by
    simp [check_digits_01] at h
    have hd' : d' = 0 ∨ d' = 1 := by
      rcases Bool.and_eq_true.mp h with ⟨h1, _⟩
      cases h_or : d' == 0
      · simp [h_or] at h1
        right; exact (beq_iff_eq.mp h1)
      · left; exact (beq_iff_eq.mp h_or)
    intro d hd
    rcases hd with rfl | h_mem
    · exact hd'
    · exact check_digits_01_ok ds (Bool.and_eq_true.mp h).2 d h_mem
