import Mathlib

open Nat

def p (k : ℕ) : ℕ := 
  if k = 0 then 2 else
  if k = 1 then 3 else
  if k = 2 then 5 else
  if k = 3 then 7 else
  if k = 4 then 11 else
  if k = 5 then 13 else
  if k = 6 then 17 else
  if k = 7 then 19 else
  if k = 8 then 23 else
  if k = 9 then 29 else 31

def A319524_computable (n : ℕ) : ℕ :=
  let Pn    := p (n - 1)
  let Pnp1  := p n
  let Pnp2  := p (n + 1)
  let S := List.range 1000 |>.filter (fun x => 
    (x > Pn) ∧ (x > Pnp1) ∧ 
    ((x - Pn) % Pnp1 == 0) ∧ 
    ((x - Pnp1) % Pnp2 == 0)
  )
  S.head!

#eval A319524_computable 1
#eval A319524_computable 2
#eval A319524_computable 7
#eval A319524_computable 8

