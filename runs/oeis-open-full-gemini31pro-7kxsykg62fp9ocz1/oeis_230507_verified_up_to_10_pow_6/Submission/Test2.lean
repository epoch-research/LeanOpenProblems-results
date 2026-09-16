import Submission.Spec
open OeisA230507

def isPrimeFast (n : ℕ) : Bool :=
  if n < 2 then false
  else if n = 2 || n = 3 then true
  else if n % 2 = 0 || n % 3 = 0 then false
  else
    let rec loop (i : ℕ) : Bool :=
      if i * i > n then true
      else if n % i = 0 || n % (i + 2) = 0 then false
      else loop (i + 6)
    loop 5

def check_loop (n : ℕ) : Bool :=
  let rec go (i : ℕ) : Bool :=
    if i = 0 then true
    else
      if isPrimeFast i then go (i - 1)
      else go (i - 1)
  go n

#eval check_loop 1000000
