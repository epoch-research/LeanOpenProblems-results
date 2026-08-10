import FormalConjectures.Util.ProblemImports

instance : CharP PUnit 1 where
  cast_eq_zero_iff x := by
    constructor
    · intro _; exact one_dvd x
    · intro _; cases (x : PUnit); rfl

#synth NoZeroDivisors PUnit
#synth CharP PUnit 1
-- This would prove Nat.Prime 1 only with impossible 2 ≤ 1.
example : ¬ (2 ≤ (1 : ℕ)) := by norm_num
example : Nat.Prime 1 := by
  fail_if_success exact CharP.char_is_prime_of_two_le PUnit 1 (by norm_num)
  exact False.elim (by norm_num)
