import Submission.Spec

def my_nth_prime (n : ℕ) : ℕ :=
  if n = 1 then 3 else if n = 2 then 5 else if n = 3 then 7 else 11

def a_comp (n : ℕ) : ℕ :=
  if 1 < n then
    let p_n : ℕ := my_nth_prime (n - 1)
    let p_z : ℤ := p_n
    let sum_q : ℤ := Finset.sum (Finset.range (p_n - 1)) (fun k : ℕ => fermat_quotient_int (k + 1) p_n)
    let L_p : ℤ := sum_q - wilson_quotient_int p_n
    (L_p / p_z).natAbs
  else
    0

#eval a_comp 4
