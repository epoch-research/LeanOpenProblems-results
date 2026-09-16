import Submission.Spec
open Nat Int Rat

def A275460_rational_c : ℕ → ℚ
  | 0 => 1
  | Nat.succ k =>
    let n : ℕ := k + 1
    let a_prev : ℚ := A275460_rational_c k
    let n_q : ℚ := n
    let num : ℚ := 3 * (9 * n_q - 7) * (9 * n_q - 5) * (9 * n_q - 2)
    let den : ℚ := n_q^2 * (3 * n_q - 2)
    a_prev * (num / den)

#eval A275460_rational_c 1
#eval A275460_rational_c 2
