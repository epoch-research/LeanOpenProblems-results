import Mathlib

set_option maxRecDepth 100000

def has_valid_pair (d : ℕ) : Bool :=
  let primes := [2, 3, 5, 7, 11, 13, 17]
  primes.any (fun p =>
    primes.any (fun q =>
      p < q ∧ d % p ≠ 0 ∧ d % q ≠ 0 ∧ p * q ≤ 150 ∧ p % 10 ≠ q % 10
    )
  )

theorem all_d_checked : ((List.range 2026).drop 1).all has_valid_pair = true := by decide
