import Submission.Spec
open Nat Finset

def a_comp (n : ℕ) : ℚ :=
  if n = 0 then 0
  else
    let numerator_sum : ℚ :=
      Finset.sum (range n) (fun k : ℕ =>
        let T1k : ℚ := T_k k 14 1
        let T2k : ℚ := T_k k 17 16

        let k_q : ℚ := k
        -- We use casting for the exponent subtraction to ensure it stays non-negative when k <= n-1
        let n_prime : ℕ := n - 1 - k

        let term_factor : ℚ := 4290 * k_q + 367
        let power_factor : ℚ := (3136 : ℚ) ^ n_prime
        let central_binomial : ℚ := (Nat.choose (2 * k) k : ℚ)

        term_factor * power_factor * central_binomial * T1k * T2k)

    let divisor : ℚ := (n : ℚ) * (Nat.choose (2 * n - 1) (n - 1) : ℚ)

    numerator_sum / divisor

#eval a_comp 1
#eval a_comp 2
#eval a_comp 3
#eval a_comp 4
