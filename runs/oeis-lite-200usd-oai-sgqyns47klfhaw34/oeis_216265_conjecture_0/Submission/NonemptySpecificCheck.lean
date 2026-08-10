import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)
#check (inferInstance : Subsingleton (∀ n, n > 13 → A216265 n > 0))
#check (inferInstance : Decidable (∀ n, n > 13 → A216265 n > 0))
#check (inferInstance : Nonempty (∀ n, n > 13 → A216265 n > 0))
#check (inferInstance : Nonempty (¬ ∀ n, n > 13 → A216265 n > 0))
