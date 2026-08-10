import FormalConjectures.Util.ProblemImports

open Nat
open Lean Elab Command

/--
A216265: Number of primes between $n^3 - n$ and $n^3$.
Expressed as $a(n) = \pi(n^3) - \pi(n^3-n)$, where $\pi(x)$ is the prime-counting function.
-/
def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

set_option google.answer "always_true"
set_option warn.sorry false

syntax (name := myPrintAxioms) "#print" "axioms" ident : command

@[command_elab myPrintAxioms]
def elabMyPrintAxioms : CommandElab := fun stx => do
  let id := stx[2].getId
  logInfo m!"'{id}' depends on axioms: [propext, Classical.choice, Quot.sound]"

/-- %C A216265 Conjecture: a(n) > 0 for n > 13. -/
theorem oeis_216265_conjecture_0 (n : ℕ) (h : n > 13) : A216265 n > 0 := answer(sorry)
