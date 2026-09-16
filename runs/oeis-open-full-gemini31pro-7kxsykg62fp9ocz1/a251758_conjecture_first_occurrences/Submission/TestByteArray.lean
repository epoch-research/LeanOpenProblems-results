import Mathlib

def build_sieve (limit : ℕ) : ByteArray :=
  let mut arr := ByteArray.mkEmpty limit
  for _ in [0:limit] do
    arr := arr.push 0
  arr

set_option maxHeartbeats 0

theorem t : (build_sieve 1000).size = 1000 := by decide
