import FormalConjectures.Util.ProblemImports

open Nat

def A030101 (n : ℕ) : ℕ :=
  Nat.ofDigits 2 (List.reverse (Nat.digits 2 n))

def a : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | n + 2 => (a n).xor (A030101 (a (n + 1))) + 1
termination_by n => n

-- Copy over the needed lemmas from test_even_lt.lean
-- [OMITTED FOR BREVITY, WILL CONSTRUCT SHORTLY]
