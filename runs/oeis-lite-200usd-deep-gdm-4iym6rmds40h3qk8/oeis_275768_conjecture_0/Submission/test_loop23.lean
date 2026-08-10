import FormalConjectures.Util.ProblemImports

def a_test (n : ℕ) : ℕ := 0

theorem test_let_rec (n : ℕ) (h : a_test n = 4) : False := by
  let rec f (x : PLift (a_test n = 4)) : PLift False := f x
  exact (f ⟨h⟩).down
