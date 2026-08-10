import FormalConjectures.Util.ProblemImports
open Nat
def tribonacci (n : ℕ) : ℕ :=
  match n with | 0=>0 | 1=>0 | 2=>1 | n+3 => tribonacci (n+2)+tribonacci (n+1)+tribonacci n
def a (n : ℕ) : ℕ := let T:=tribonacci n; if h:T≤1 then 0 else let j:=T.log2-1; if T.testBit j then 1 else 0
example : a 6 = 1 := by native_decide
example : a 13 ≠ 0 := by native_decide
