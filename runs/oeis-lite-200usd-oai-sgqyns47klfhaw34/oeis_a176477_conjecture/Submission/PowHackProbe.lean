import FormalConjectures.Util.ProblemImports
open Nat
instance (priority := 2000) badPowNat : Pow ℕ ℕ where pow _ _ := 1
#check (fun (n m : ℕ) => n = 2^m)
#eval (2:ℕ)^3
