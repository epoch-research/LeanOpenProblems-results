import FormalConjectures.Util.ProblemImports

def f_1 (n : ℕ) : Bool := true
def f_2 (n : ℕ) : Bool := false

def f (n : ℕ) : Bool :=
  if n < 20000 then f_1 n else f_2 n

theorem claim_1 : ∀ n, n < 20000 → f n = true := by
  intro n hn
  dsimp [f]
  rw [if_pos hn]
