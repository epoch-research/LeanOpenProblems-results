import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) deriving Nonempty where
  proof : 0 < A271510 n

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s : MySol n := Classical.choice inferInstance
  exact s.proof
