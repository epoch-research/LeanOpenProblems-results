import Submission.Spec

def get_divisors_aux (n : ℕ) (d : ℕ) (acc1 acc2 : List ℕ) : List ℕ :=
  if d * d > n then
    acc1.reverse ++ acc2
  else if d * d = n then
    acc1.reverse ++ (d :: acc2)
  else if n % d = 0 then
    get_divisors_aux n (d + 1) (d :: acc1) ((n / d) :: acc2)
  else
    get_divisors_aux n (d + 1) acc1 acc2
termination_by n - d
decreasing_by
  sorry

def get_div_fast (n : ℕ) : List ℕ :=
  get_divisors_aux n 1 [] []

def a_fast (n : ℕ) : ℕ :=
  let divs := get_div_fast n
  let s := (divs.zip divs.tail).foldl (fun acc p => acc + p.fst * p.snd) 0
  if s = 0 then 0 else n * n / s

#eval a_fast 6678671
