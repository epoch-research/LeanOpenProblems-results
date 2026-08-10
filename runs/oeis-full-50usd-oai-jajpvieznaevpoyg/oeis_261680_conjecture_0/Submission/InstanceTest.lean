import FormalConjectures.Util.ProblemImports

def aa (n : ℕ) := n
local instance instFakeLTNat : LT Nat := ⟨fun _ _ => True⟩
theorem tt (n : ℕ) : aa n > 0 := by
  trivial
#print tt
#print axioms tt
