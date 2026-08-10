import Mathlib
open Nat
-- Confirm: for prime n, 1 + totient n = n, so the conjecture demands a prime in (n^2, n^2+n].
example : Nat.totient 101 = 100 := by decide
example : 1 + Nat.totient 101 = 101 := by decide
-- The least prime above 101^2 = 10201:
-- 10201..10301 : is there a prime <= 10201+100 = 10301?  (Oppermann for n=101)
#eval (List.range 102).filter (fun k => k > 0 && Nat.Prime (10201 + k))
-- For n=101 the smallest gap prime is at k=?
#eval (List.range 200).find? (fun k => k > 0 && Nat.Prime (10201 + k))
