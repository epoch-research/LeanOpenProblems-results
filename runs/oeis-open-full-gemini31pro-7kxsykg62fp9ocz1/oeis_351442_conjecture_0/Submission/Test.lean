import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma gcd_test : (8192 : ℕ).gcd 729 = 1 := by norm_num
