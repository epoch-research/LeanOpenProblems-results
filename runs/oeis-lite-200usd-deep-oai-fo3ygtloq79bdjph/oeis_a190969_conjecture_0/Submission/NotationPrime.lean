import FormalConjectures.Util.ProblemImports
postfix:max ".Prime" => False
example (p : ℕ) (hp : p.Prime) : False := hp
#check Nat.Prime
#check (fun p : ℕ => p.Prime)
