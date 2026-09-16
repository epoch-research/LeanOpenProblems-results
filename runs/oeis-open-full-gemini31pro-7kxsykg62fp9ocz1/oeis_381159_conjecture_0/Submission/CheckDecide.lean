import Mathlib

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

def check_pair (p q : ℕ) : Bool :=
  if p * q ≤ 150 ∧ p ≠ q then
    let pq := p * q
    (List.range pq).all (fun a =>
      (List.range pq).all (fun d =>
        if d % p ≠ 0 ∧ d % q ≠ 0 then
          (List.range 150).any (fun i => (a + i * d) % p == 0 ∧ (a + i * d) % q == 0)
        else true
      )
    )
  else true

theorem all_pairs_good :
  let primes := [2, 3, 5, 7, 11, 13, 17]
  primes.all (fun p => primes.all (fun q => check_pair p q)) = true := by decide
