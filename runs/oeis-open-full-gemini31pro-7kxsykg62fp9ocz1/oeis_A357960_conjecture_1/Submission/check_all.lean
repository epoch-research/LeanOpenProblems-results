import Submission.Spec
open Nat

partial def is_prime (n : ℕ) : Bool :=
  if n < 2 then false
  else
    let rec loop (i : ℕ) : Bool :=
      if i * i > n then true
      else if n % i == 0 then false
      else loop (i + 1)
    loop 2

partial def check_all_up_to (m : ℕ) : Bool :=
  let rec loop (p : ℕ) : Bool :=
    if p > m then true
    else if is_prime p && p ≥ 3 then
      if (a p) % (p ^ 5) != (a 1) % (p ^ 5) then false
      else loop (p + 1)
    else loop (p + 1)
  loop 2

#eval! check_all_up_to 100
