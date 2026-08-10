import FormalConjectures.Util.ProblemImports

def vals : List ℕ := [10, 20, 30, 40, 50]
def C : ℕ := 999

def a (n : ℕ) : ℕ :=
  if h : n < vals.length then
    vals.get ⟨n, h⟩
  else
    C

theorem test_eval_large (n : ℕ) (hn : 5 ≤ n) : a n = 999 := by
  unfold a
  have h_not : ¬ n < vals.length := by
    have : vals.length = 5 := by rfl
    omega
  rw [dif_neg h_not]
  rfl
