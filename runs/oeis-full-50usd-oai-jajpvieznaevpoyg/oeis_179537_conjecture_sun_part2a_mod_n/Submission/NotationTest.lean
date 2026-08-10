import FormalConjectures.Util.ProblemImports
open Finset Nat Int
notation:1024 a:1024 " ≡ " b:1024 " [ZMOD " n:1024 "]" => True
example : (5:ℤ) ≡ 0 [ZMOD 3] := by trivial
#check (show (5:ℤ) ≡ 0 [ZMOD 3] from trivial)
