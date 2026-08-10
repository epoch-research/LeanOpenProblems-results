import FormalConjectures.Util.ProblemImports

def A335624_rep (n : ℕ) : Prop :=
  ∃ x y z w : ℕ, x^2 + y^2 + z^2 + w^2 = n ∧ Nat.sqrt (x + 3 * y + 4 * z) ^ 2 = x + 3 * y + 4 * z

example : A335624_rep 2 := by
  use 0, 0, 1, 1
  constructor <;> norm_num
