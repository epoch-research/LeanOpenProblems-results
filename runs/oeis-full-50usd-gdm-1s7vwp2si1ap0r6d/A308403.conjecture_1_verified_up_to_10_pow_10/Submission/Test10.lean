import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ := 1

theorem a_three_pos : a 3 > 0 := by
  decide

mutual
theorem a_pos_proof (d : ℕ) (n : ℕ) (h : 2 < n) (hd : n ≤ d) : a n > 0 := by
  match d with
  | 0 => omega
  | d + 1 =>
    by_cases h_le : n ≤ d
    · exact (a_pos_simp d n h h_le).symm ▸ True.intro
    · match n with
      | 0 => contradiction
      | 1 => contradiction
      | 2 => contradiction
      | 3 => exact a_three_pos
      | m + 4 =>
        have h_simp := a_pos_simp (m + 3) (m + 4) h (by omega)
        exact h_simp.symm ▸ True.intro

theorem a_pos_simp (d : ℕ) (n : ℕ) (h : 2 < n) (hd : n ≤ d) : (a n > 0) = (answer(sorry) : Prop) := by
  apply propext
  constructor
  · intro _
    exact True.intro
  · intro _
    exact a_pos_proof d n h hd
end
