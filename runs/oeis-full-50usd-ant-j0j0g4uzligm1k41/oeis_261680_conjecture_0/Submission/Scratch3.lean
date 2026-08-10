import FormalConjectures.Util.ProblemImports
open Nat List

theorem inflate_value (c : List ℕ) :
    Nat.ofDigits 2 ((1 :: c) ++ [1]) = 1 + 2 * Nat.ofDigits 2 c + 2^(c.length + 1) := by
  rw [show (1 :: c) ++ [1] = 1 :: (c ++ [1]) from rfl, Nat.ofDigits_cons, Nat.ofDigits_append,
      Nat.ofDigits_cons, Nat.ofDigits_nil, pow_succ]
  ring
