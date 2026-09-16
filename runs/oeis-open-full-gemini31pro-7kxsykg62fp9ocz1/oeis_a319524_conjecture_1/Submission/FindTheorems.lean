import Mathlib
import FormalConjecturesForMathlib.NumberTheory.PrimeGap

open Lean Meta Elab Command

elab "find_prime_gap_lemmas" : command => do
  let env ← getEnv
  let mut count := 0
  for (n, c) in env.constants.toList do
    if n.toString.containsSubstr "primeGap" then
      count := count + 1
      IO.println n.toString
  IO.println s!"Found {count} lemmas"

find_prime_gap_lemmas
