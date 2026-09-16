import Submission.Spec
open Nat

def T1_0 : ℚ := T_k 0 14 1
def T2_0 : ℚ := T_k 0 17 16

def t_0_rat : ℚ :=
  let term_factor : ℚ := 4290 * 0 + 367
  let power_factor : ℚ := (3136 : ℚ) ^ 0
  let central_binomial : ℚ := (Nat.choose 0 0 : ℚ)
  term_factor / power_factor * central_binomial * T1_0 * T2_0

#eval t_0_rat

def T1_1 : ℚ := T_k 1 14 1
def T2_1 : ℚ := T_k 1 17 16

def t_1_rat : ℚ :=
  let term_factor : ℚ := 4290 * 1 + 367
  let power_factor : ℚ := (3136 : ℚ) ^ 1
  let central_binomial : ℚ := (Nat.choose 2 1 : ℚ)
  term_factor / power_factor * central_binomial * T1_1 * T2_1

#eval t_1_rat
