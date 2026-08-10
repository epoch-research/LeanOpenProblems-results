import FormalConjectures.Util.ProblemImports

open Nat

def totient_on_the_fly_loop (n : Nat) (d : Nat) (acc : Nat) : Nat → Nat
  | 0 => acc
  | fuel + 1 =>
    if d * d > n then
      if n > 1 then acc - acc / n else acc
    else if n % d == 0 then
      let acc' := acc - acc / d
      let rec remove_d : Nat → Nat → Nat
        | 0, temp => temp
        | f + 1, temp =>
          if temp % d == 0 then remove_d f (temp / d) else temp
      let n' := remove_d 32 (n / d)
      totient_on_the_fly_loop n' (d + 1) acc' fuel
    else
      totient_on_the_fly_loop n (d + 1) acc fuel

def totient_on_the_fly (n : Nat) : Nat :=
  if n == 0 then 0
  else if n == 1 then 1
  else totient_on_the_fly_loop n 2 n n

def run_on_the_fly : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | i + 1, cur, acc => run_on_the_fly i (cur + 1) (acc + totient_on_the_fly cur)

#eval run_on_the_fly 1000 100000 0

