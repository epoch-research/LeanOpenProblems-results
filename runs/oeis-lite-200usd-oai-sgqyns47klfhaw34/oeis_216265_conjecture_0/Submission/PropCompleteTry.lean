import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

example : (∀ n, n > 13 → A216265 n > 0) := by
  classical
  let P := (∀ n, n > 13 → A216265 n > 0)
  have hc := Classical.propComplete P
  change P
  rcases hc with htrue | hfalse
  · rw [htrue]
    trivial
  · rw [hfalse]
    -- goal False
    fail_if_success trivial
    exact False.elim (by contradiction)
