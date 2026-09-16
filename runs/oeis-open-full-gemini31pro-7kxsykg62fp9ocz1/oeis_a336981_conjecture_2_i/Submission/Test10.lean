import Submission.Spec
open Nat

def T1_2 : ℚ := T_k 2 14 1
def T2_2 : ℚ := T_k 2 17 16

def t_2_rat : ℚ :=
  let term_factor : ℚ := 4290 * 2 + 367
  let power_factor : ℚ := (3136 : ℚ) ^ 2
  let central_binomial : ℚ := (Nat.choose 4 2 : ℚ)
  term_factor / power_factor * central_binomial * T1_2 * T2_2

#eval t_2_rat
