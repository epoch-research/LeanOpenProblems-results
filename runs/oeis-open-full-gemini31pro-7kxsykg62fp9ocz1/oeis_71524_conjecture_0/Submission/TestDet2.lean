import FormalConjectures.Util.ProblemImports
open Matrix Nat
def M (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j =>
  let i_idx : ℕ := i.val + 1
  let j_idx : ℕ := j.val + 1
  if (i_idx ^ 2 + j_idx ^ 2).Prime then (1 : ℤ) else (0 : ℤ)

#eval (M 7).det
#eval (M 8).det
#eval (M 9).det
#eval (M 10).det
