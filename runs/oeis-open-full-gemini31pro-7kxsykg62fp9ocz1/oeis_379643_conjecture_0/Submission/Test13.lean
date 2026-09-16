import Submission.Spec

partial def isPrimeFast (n : ℕ) : Bool :=
  if n < 2 then false
  else if n == 2 then true
  else if n % 2 == 0 then false
  else
    let rec check (k : ℕ) : Bool :=
      if k * k > n then true
      else if n % k == 0 then false
      else check (k + 2)
    check 3

partial def findCounterexample : ℕ :=
  let rec loop (n : ℕ) (p : ℕ) (c1 c3 c5 c7 : ℕ) : ℕ :=
    if n > 1000000 then 0
    else
      let rec nextPrime (k : ℕ) : ℕ :=
        if isPrimeFast k then k else nextPrime (k + 1)
      let p_n := nextPrime (p + 1)
      let m := p_n % 8
      let nc1 := if m == 1 then c1 + 1 else c1
      let nc3 := if m == 3 then c3 + 1 else c3
      let nc5 := if m == 5 then c5 + 1 else c5
      let nc7 := if m == 7 then c7 + 1 else c7
      
      let a := (nc3 : ℤ) - (nc7 : ℤ)
      let b := (nc5 : ℤ) - (nc1 : ℤ)
      
      if a == 0 && b < 0 then n
      else loop (n + 1) p_n nc1 nc3 nc5 nc7
  loop 1 1 0 0 0 0

#eval! findCounterexample
