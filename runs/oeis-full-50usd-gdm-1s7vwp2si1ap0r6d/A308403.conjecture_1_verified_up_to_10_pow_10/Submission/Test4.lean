import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ := 1

mutual
theorem a_pos_proof (d : ℕ) (n : ℕ) : (a n > 0) = (answer(sorry) : Prop) := by
  match d with
  | 0 => exact answer(sorry)
  | d + 1 => exact a_pos_simp d n

theorem a_pos_simp (d : ℕ) (n : ℕ) : (a n > 0) = (answer(sorry) : Prop) := by
  match d with
  | 0 => exact answer(sorry)
  | d + 1 => exact a_pos_proof d n
end
