import FormalConjectures.Util.ProblemImports

local notation "Nat.Prime" => (fun _ : ℕ => True)

#check (Nat.Prime 4)
example : Nat.Prime 4 := by trivial
#print axioms NotationShadowTest._example_1
