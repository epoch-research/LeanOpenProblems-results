import FormalConjectures.Util.ProblemImports

open Nat BigOperators

-- Copy the definition of a to Test.lean so we can use it
def a_test (n : ℕ) : ℕ :=
  let B (k : ℕ) : ℕ := (2 * k + 1).choose k
  let R_sq := Finset.range (n.sqrt + 1)
  let R_binom := Finset.range (n + 1)
  R_sq.sum fun a =>
    R_sq.sum fun b =>
      R_binom.sum fun c =>
        R_binom.sum fun d =>
          if a ≤ b ∧ c ≤ d ∧ a ^ 2 + b ^ 2 + B c + B d = n then 1 else 0


#reduce a_test 2

#eval a_test 2
#eval a_test 3
#eval a_test 4
#eval a_test 5
#eval a_test 6

theorem a_test_2 : a_test 2 > 0 := by
  unfold a_test
  norm_num
  decide

theorem a_test_3 : a_test 3 > 0 := by
  unfold a_test
  norm_num
  decide


set_option maxRecDepth 200000

theorem a_test_100 : a_test 100 > 0 := by
  unfold a_test
  norm_num
  decide







