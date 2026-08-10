import FormalConjectures.Util.ProblemImports
open Nat

-- Can we produce a false-looking theorem about standard Nat operations via local instance/notation? It should elaborate with hacked operations or fail.
section Hack
local instance (priority := high) : Pow Nat Nat := ⟨fun _ _ => 0⟩
local instance (priority := high) : Sub Nat := ⟨fun _ _ => 3⟩
local instance (priority := high) : Mul Nat := ⟨fun _ _ => 4⟩
local instance (priority := high) : Add Nat := ⟨fun _ _ => 5⟩

@[simp] theorem hacked_expr_eq (n k : ℕ) : ((3 ^ n - k) * (2 ^ n) - 1) = 3 := rfl
#print hacked_expr_eq
set_option pp.all true in #print hacked_expr_eq
end Hack

example (n : ℕ) (hn : n > 0) :
    ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1) := by
  use 0
  simp?
