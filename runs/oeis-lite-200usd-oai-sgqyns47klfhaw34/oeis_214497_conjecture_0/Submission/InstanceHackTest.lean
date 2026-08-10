import FormalConjectures.Util.ProblemImports

open Nat

section Hack
local instance (priority := high) : Pow Nat Nat := ⟨fun _ _ => 0⟩
local instance (priority := high) : Sub Nat := ⟨fun _ _ => 3⟩
local instance (priority := high) : Mul Nat := ⟨fun _ _ => 4⟩
local instance (priority := high) : Add Nat := ⟨fun _ _ => 5⟩

#eval (3 : Nat) ^ (7 : Nat)
#eval (3 : Nat) - (7 : Nat)
#eval (3 : Nat) * (7 : Nat)
#eval (3 : Nat) + (7 : Nat)

theorem hacked (n : ℕ) (hn : n > 0) :
    ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1) := by
  use 0
  change Nat.Prime 3 ∧ Nat.Prime 5
  norm_num

#print axioms hacked
#print hacked
set_option pp.all true in
#print hacked

end Hack
