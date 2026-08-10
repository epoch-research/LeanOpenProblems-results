import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 300000
set_option maxHeartbeats 30000000

open Nat Set

/--
A268597: Smallest $x$ such that $x-1 \pmod{\phi(x)} = n$, or $0$ if no such $x$ exists.
-/
noncomputable def A268597 (n : ℕ) : ℕ := 
  sInf { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n }

/--
A268597 Conjecture: a(n) > 0 for all n.
-/
theorem oeis_268597_conjecture_0 (n : ℕ) : A268597 n > 0 := answer(sorry)

#print axioms oeis_268597_conjecture_0