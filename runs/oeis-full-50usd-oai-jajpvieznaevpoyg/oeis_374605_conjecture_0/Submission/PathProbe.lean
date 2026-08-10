import FormalConjectures.Util.ProblemImports
-- Can local notation/macro shadow Nat.Prime? (Expect no effect / parse failure)
local notation "Nat.Prime" => fun _ : ℕ => False
example (p : ℕ) (hp : Nat.Prime p) : False := hp
