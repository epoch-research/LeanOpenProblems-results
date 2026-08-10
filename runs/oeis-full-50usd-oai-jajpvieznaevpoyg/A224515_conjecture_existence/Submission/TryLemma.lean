import FormalConjectures.Util.ProblemImports
open Nat
example (k M t d : Nat) (hM : M = 2*t+1) (hd : d = k^2 &&& M) (h : k + d = t) :
    Nat.xor (k^2) ((k+1)^2) = M := by
  -- try using testBit?
  have hdiff : (k+1)^2 = k^2 + M - 2*d := by omega
  rw [hdiff]
  subst d
  -- goal: k^2 ^^^ (k^2 + M - 2*(k^2&&&M)) = M
  -- exact ?_
  sorry
