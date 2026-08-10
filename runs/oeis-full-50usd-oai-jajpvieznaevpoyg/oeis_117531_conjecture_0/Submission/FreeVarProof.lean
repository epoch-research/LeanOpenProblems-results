import Mathlib
variable (H : ∀ n : Nat, n = n+1)
theorem weird (n : Nat) : n = n+1 := by exact H n
#print weird
#print axioms weird
