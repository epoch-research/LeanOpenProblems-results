import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ := 1

theorem a_three_pos : a 3 > 0 := by
  decide

mutual
theorem a_pos_proof (n : ℕ) (h : 2 < n) : a n > 0 := by
  match n with
  | 0 => contradiction
  | 1 => contradiction
  | 2 => contradiction
  | 3 => exact a_three_pos
  | n + 4 => exact (a_pos_simp (n + 4) h).symm ▸ True.intro

theorem a_pos_simp (n : ℕ) (h : 2 < n) : (a n > 0) = (answer(sorry) : Prop) := by
  apply propext
  constructor
  · intro _
    exact True.intro
  · intro _
    match n with
    | 0 => contradiction
    | 1 => contradiction
    | 2 => contradiction
    | 3 => exact a_three_pos
    | n + 4 => exact a_pos_proof (n + 4) h
end
