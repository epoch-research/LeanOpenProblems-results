import Submission.Spec
open Nat

def check_val (n k p : ℕ) : Bool :=
  let lhs : ℤ := A003162.b (n * p ^ k)
  let rhs : ℤ := A003162.b (n * p ^ (k - 1))
  let m : ℤ := (p : ℤ) ^ (3 * k)
  lhs ≡ rhs [ZMOD m]

def search : IO Unit := do
  let primes := [5, 7, 11]
  for p in primes do
    for k in [1, 2] do
      for n in List.range 15 do
        let n := n + 1
        if !check_val n k p then
          IO.println s!"COUNTEREXAMPLE: n={n}, k={k}, p={p}"
          return
  IO.println "Done."

#eval! search
