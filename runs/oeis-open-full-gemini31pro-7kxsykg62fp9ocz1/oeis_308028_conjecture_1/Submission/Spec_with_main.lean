import FormalConjectures.Util.ProblemImports
open Nat Finset

/--
A308028: Number of ways to write $2n+1$ as $p + q + r$ with $2p + 4q + 6r$ a square, where $p,q,r$ are odd primes.
-/
def A308028 (n : ℕ) : ℕ :=
  let N := 2 * n + 1

  -- Summation over all possible natural numbers p and q up to N.
  (range (N + 1)).sum fun p =>
    (range (N + 1)).sum fun q =>
      -- Check if p + q leaves a positive remainder r.
      if p + q < N then
        let r := N - p - q
        let C := 2 * p + 4 * q + 6 * r

        -- Check all conditions: p, q, r are odd primes AND 2p+4q+6r is a square.
        if (p.Prime ∧ p ≠ 2) ∧
           (q.Prime ∧ q ≠ 2) ∧
           (r.Prime ∧ r ≠ 2) ∧
           (C.sqrt * C.sqrt = C)
        then 1 else 0
      else 0

/--
The 2-4-6 Conjecture: a(n) > 0 for all n > 6. In other words, any odd integer greater than 14 can be written as the sum of three odd primes p,q,r for which 2*p + 4*q + 6*r is an integer square.
-/
theorem oeis_308028_conjecture_1 : ∀ (n : ℕ), 6 < n → 0 < A308028 n :=
by sorry

theorem oeis_308028_conjecture_1.disproof : ¬ (type_of% @oeis_308028_conjecture_1) := sorry
#eval A308028 7
#eval A308028 8
#eval A308028 9
#eval A308028 10
#eval A308028 11
#eval A308028 12
#eval A308028 13
#eval A308028 14
def check_range_spec : ℕ → IO Unit
| 0 => pure ()
| n + 1 => do
  if n > 6 then
    let res := A308028 n
    if res == 0 then
      IO.println s!"COUNTEREXAMPLE IN LEAN: n = {n}"
  check_range_spec n

#eval! check_range_spec 500
def test_eval : IO Unit := do
  IO.println s!"Starting test"
  for n in [7:50] do
    if A308028 n == 0 then
      IO.println s!"COUNTEREXAMPLE: {n}"
  IO.println s!"Finished test"

#eval! test_eval
def find_counterexample : IO Unit := do
  for n in [7:2000] do
    if A308028 n == 0 then
      IO.println s!"COUNTEREXAMPLE IN LEAN: {n}"
  IO.println "DONE 2000"

#eval! find_counterexample
def fast_check : IO Unit := do
  let mut max_n := 0
  for n in [7:2000] do
    let res := A308028 n
    if res == 0 then
      IO.println s!"COUNTEREXAMPLE: {n}"
      break
  IO.println "DONE CHECK"

#eval! fast_check
def main : IO Unit := do
  for n in [7:2000] do
    let res := A308028 n
    if res == 0 then
      IO.println s!"COUNTEREXAMPLE: {n}"
      return
  IO.println "DONE CHECK"
