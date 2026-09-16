import Mathlib

def check_pair (p q d : ℕ) : Bool :=
  let pq := p * q
  (List.range pq).all (fun a =>
    (List.range pq).any (fun i => (a + i * d) % p == 0 ∧ (a + i * d) % q == 0)
  )

#eval check_pair 2 3 1
