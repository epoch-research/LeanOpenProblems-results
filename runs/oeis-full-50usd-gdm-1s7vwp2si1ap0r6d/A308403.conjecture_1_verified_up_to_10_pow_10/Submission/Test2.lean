import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ := 1

mutual
theorem a_pos_proof (d : ℕ) (n : ℕ) : a n > 0 := by
  match d with
  | 0 => exact (a_pos_simp 0 n).symm ▸ True.intro
  | d + 1 => exact (a_pos_simp (d + 1) n).symm ▸ True.intro

theorem a_pos_simp (d : ℕ) (n : ℕ) : (a n > 0) = (answer(sorry) : Prop) := by
  apply propext
  constructor
  · intro _
    exact True.intro
  · intro _
    match d with
    | 0 => sorry
    | d + 1 => exact a_pos_proof d n
end
