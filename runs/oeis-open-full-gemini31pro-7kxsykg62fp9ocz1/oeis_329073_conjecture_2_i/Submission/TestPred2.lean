import Submission.Spec
open Finset

def check_n (n : ℕ) : Bool :=
  if n == 0 then true else
  let b_val := A329073_b n
  let sum_val := (range n).sum fun k : ℕ =>
    let k_int : ℤ := k.cast
    let coeff_a : ℤ := T_coeff k 4 1
    let coeff_b : ℤ := T_coeff k 1 (-1)
    let term_1 := (40 * k_int + 27)
    let term_3_exp : ℕ := n - 1 - k
    let term_3 := ((-6) : ℤ) ^ term_3_exp
    term_1 * term_3 * coeff_a * (coeff_b ^ 2)
  let div_ok := sum_val % (n.cast : ℤ) == 0
  let pow2 := (n &&& (n - 1) == 0) && (n != 0)
  let odd := b_val % 2 == 1
  div_ok && (odd == pow2)

#eval! (List.range 50).all (fun i => check_n (i + 1))
