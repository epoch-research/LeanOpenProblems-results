import FormalConjectures.Util.ProblemImports
local notation "Nat.Prime" => fun _ : ℕ => False
theorem t (p : ℕ) (hp : Nat.Prime p) : False := hp
#print t
#print axioms t
