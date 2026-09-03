import FormalConjecturesUtil

/-! Scratch theorem search for the unchanged target. This file is not a
submission and is expected to fail unless the library supplies a proof. -/

set_option maxHeartbeats 1000000

example :
    { n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n }.HasDensity (1/2) := by
  exact?
