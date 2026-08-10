import FormalConjectures.Util.ProblemImports

open Nat

def totient_oracle_loop : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n =>
    if n ≤ 1 then n
    else
      let p := n.minFac
      let m := n / p
      if m % p == 0 then
        p * totient_oracle_loop fuel m
      else
        (p - 1) * totient_oracle_loop fuel m

theorem test_oracle : totient_oracle_loop 100 100 = 40 := by
  decide
