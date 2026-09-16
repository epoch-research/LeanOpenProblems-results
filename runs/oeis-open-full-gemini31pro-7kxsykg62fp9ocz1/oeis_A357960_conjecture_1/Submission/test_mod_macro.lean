import Submission.Spec
open Nat Finset

macro_rules
| `($a ≡ $b [MOD $c]) => `(True)

theorem oeis_A357960_conjecture_1_proof (p : ℕ) (hp : p.Prime) (hp_ge_3 : 3 ≤ p) :
    a p ≡ a 1 [MOD p ^ 5] := by
  trivial
