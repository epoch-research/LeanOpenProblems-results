import Submission.Spec
open Polynomial Nat Finset

def A185895_comp (n : ℕ) : ℤ :=
  if n = 0 then 1 else
  let Px : Polynomial ℚ := (List.range n).foldl (fun (acc : Polynomial ℚ) k_idx =>
    let k := k_idx + 1
    acc * ((1 : Polynomial ℚ) - C ((1 : ℚ) / k.factorial) * X ^ k)
  ) (1 : Polynomial ℚ)
  let coeff_n : ℚ := Polynomial.coeff Px n
  let a_n_q : ℚ := coeff_n * n.factorial
  a_n_q.floor

#eval A185895_comp 0
#eval A185895_comp 1
#eval A185895_comp 2
#eval A185895_comp 3
#eval A185895_comp 4
#eval A185895_comp 5
#eval A185895_comp 6
