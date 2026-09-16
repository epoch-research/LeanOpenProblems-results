import Submission.Spec
open OeisA230507

def isPrimeFast (n : ℕ) : Bool :=
  if n < 2 then false
  else if n = 2 || n = 3 then true
  else if n % 2 = 0 || n % 3 = 0 then false
  else
    let rec loop (i : ℕ) : Bool :=
      if i * i > n then true
      else if n % i == 0 || n % (i + 2) == 0 then false
      else loop (i + 6)
    loop 5
  decreasing_by sorry

def A_comp (n : ℕ) : Bool :=
  let rec loop_a (a : ℕ) : Bool :=
    if a > n / 3 then false
    else
      let rec loop_b (b : ℕ) : Bool :=
        if b > (n - a) / 2 then false
        else
          let c := n - a - b
          if isPrimeFast (2*a+1) && isPrimeFast (2*a^3+1) &&
             isPrimeFast (2*b+1) && isPrimeFast (2*b^3+1) &&
             isPrimeFast (2*c+1) && isPrimeFast (2*c^3+1) then true
          else loop_b (b + 1)
      if loop_b a then true
      else loop_a (a + 1)
  loop_a 1
  decreasing_by sorry

#eval A_comp 1000
