import FormalConjectures.Util.ProblemImports

open Nat

def a (n : ℕ) : ℕ :=
  let N : ℕ := 2 * n - 1
  let B : ℕ := N.log2 + 1

  let X_range : Finset ℕ := Finset.Icc 1 B
  let Y_range : Finset ℕ := Finset.Icc 1 B

  (Finset.product X_range Y_range).sum fun pair =>
    let x := pair.fst
    let y := pair.snd

    let sum_of_powers := 2 ^ x + 11 * 2 ^ y

    if N > sum_of_powers then
      let p := N - sum_of_powers
      if Nat.Prime p ∧ p % 6 = 1 then 1 else 0
    else
      0

#eval a 59586
#eval a 59587
#eval a 59588
#eval a 59589
#eval a 59590
#eval a 59591
#eval a 59592
#eval a 59593
#eval a 59594
#eval a 59595
#eval a 59596
#eval a 59597
#eval a 59598
#eval a 59599
#eval a 59600

theorem not_prime_35 : ¬ Nat.Prime 35 := by
  apply Nat.not_prime_of_mul_eq (a := 5) (b := 7)
  · rfl
  · decide
  · decide


