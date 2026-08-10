import FormalConjectures.Util.ProblemImports

open Nat

set_option pp.all true

#check (fun (n : ℕ) (hn : n > 0) =>
  (show Prop from ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)))

#check Nat.Prime
#print Nat.Prime
#print HPow.hPow
#print instPowNat
#print Nat.instPow
#print Nat.pow
#print instSubNat
#print instMulNat
#print instAddNat
