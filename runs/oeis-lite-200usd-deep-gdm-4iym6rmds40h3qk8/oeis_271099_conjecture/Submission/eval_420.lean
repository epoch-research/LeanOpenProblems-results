import FormalConjectures.Util.ProblemImports

open Nat Finset

def A271099_eval (n : ℕ) : ℕ :=
  let R := Finset.range (n + 1)
  Finset.sum R fun u =>
  Finset.sum R fun v =>
  Finset.sum R fun x =>
  Finset.sum R fun y =>
  Finset.sum R fun z =>
    if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = n then
      1
    else
      0

#eval A271099_eval 0
#eval A271099_eval 1
#eval A271099_eval 10
#eval A271099_eval 14
#eval A271099_eval 15
#eval A271099_eval 17
#eval A271099_eval 22
#eval A271099_eval 38
#eval A271099_eval 39
#eval A271099_eval 45
#eval A271099_eval 47
#eval A271099_eval 50
#eval A271099_eval 52
