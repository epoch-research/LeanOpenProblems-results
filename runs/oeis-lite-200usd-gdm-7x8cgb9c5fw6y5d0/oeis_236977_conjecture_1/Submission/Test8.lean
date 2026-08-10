import FormalConjectures.Util.ProblemImports

open Nat

partial def totient_fast (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n = 1 then 1
  else totient_loop n 2 n
where
  totient_loop (temp : ℕ) (p : ℕ) (acc : ℕ) : ℕ :=
    if p * p > temp then
      if temp > 1 then acc - acc / temp else acc
    else if temp % p = 0 then
      let acc' := acc - acc / p
      let rec remove_p (t : ℕ) : ℕ :=
        if t % p = 0 then remove_p (t / p) else t
      totient_loop (remove_p temp) (p + 1) acc'
    else
      totient_loop temp (p + 1) acc

#eval totient_fast 9
#eval totient_fast 1000000
