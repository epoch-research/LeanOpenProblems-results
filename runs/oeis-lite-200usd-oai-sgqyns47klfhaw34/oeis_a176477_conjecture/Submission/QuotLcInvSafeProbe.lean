import FormalConjectures.Util.ProblemImports
theorem qinvEq : Quot.lcInv (Quot.mk (fun _ _ : Nat => True) 0) = (0:Nat) := by rfl
#print axioms qinvEq
