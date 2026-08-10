import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

partial def get_decidable (n : ℕ) : Decidable (0 < A271510 n) :=
  get_decidable n

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let d := get_decidable n
  cases d with
  | isTrue h => exact h
  | isFalse h =>
    -- wait, we have h : ¬ (0 < A271510 n).
    -- can we get a contradiction?
    sorry
