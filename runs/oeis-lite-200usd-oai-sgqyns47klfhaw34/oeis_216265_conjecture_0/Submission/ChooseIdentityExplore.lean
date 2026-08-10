import FormalConjectures.Util.ProblemImports

open Nat

#check Nat.choose_mul_right
#check Nat.choose_mul_add
#check Nat.choose_succ_right_eq
#check Nat.choose_mul_succ_eq
#check Nat.add_one_mul_choose_eq
#check Nat.choose_mul

example (n : ℕ) (hn : n ≠ 0) :
    Nat.choose (n^2 * n) n = n^2 * Nat.choose (n^2 * n - 1) (n - 1) := by
  simpa [pow_two, mul_assoc] using Nat.choose_mul_right (m := n^2) (n := n) hn

-- If choose(N,n) divides m!, this identity only forces n^2 | m!, true for n≥?; not enough.
