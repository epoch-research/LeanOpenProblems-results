import FormalConjectures.Util.ProblemImports
open Finset Nat Int
macro_rules | `($a:term ≡ $b:term [ZMOD $n:term]) => `(True)
example : (5:ℤ) ≡ 0 [ZMOD 3] := by trivial
#check (show (5:ℤ) ≡ 0 [ZMOD 3] from trivial)
