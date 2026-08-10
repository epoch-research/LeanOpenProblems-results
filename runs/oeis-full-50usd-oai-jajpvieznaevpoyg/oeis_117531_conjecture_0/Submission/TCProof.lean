import Mathlib
variable [Fact (∀ n : Nat, n = n+1)]
theorem weird (n : Nat) : n = n+1 := by exact Fact.out (p := ∀ n : Nat, n = n+1) n
#print weird
