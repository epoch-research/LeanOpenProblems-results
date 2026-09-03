import Submission.RoundedSieve

/-! An exact finite rounded-moment certificate for the first fourteen primes.
This is NOT a bound for arbitrary fourteen-prime sets, or a uniform quadratic
Jacobsthal bound. The coefficient data are checked by Lean, not a numerical
solver. The factorization avoids enumerating all Boolean patterns. -/
namespace Erdos970.Rounded600
open Finset BlockSieve BlockSieve.SievePolynomial

set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

def primes : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43}

def termPrimes : Fin 72 → Finset ℕ := ![
  ∅,
  {2},
  {3},
  {2, 3},
  {5},
  {2, 5},
  {3, 5},
  {2, 3, 5},
  {7},
  {2, 7},
  {3, 7},
  {2, 3, 7},
  {5, 7},
  {2, 5, 7},
  {3, 5, 7},
  {2, 3, 5, 7},
  {11},
  {2, 11},
  {3, 11},
  {2, 3, 11},
  {5, 11},
  {2, 5, 11},
  {3, 5, 11},
  {2, 3, 5, 11},
  {13},
  {2, 13},
  {3, 13},
  {2, 3, 13},
  {5, 13},
  {2, 5, 13},
  {3, 5, 13},
  {2, 3, 5, 13},
  {17},
  {2, 17},
  {3, 17},
  {2, 3, 17},
  {5, 17},
  {2, 5, 17},
  {3, 5, 17},
  {2, 3, 5, 17},
  {19},
  {2, 19},
  {3, 19},
  {2, 3, 19},
  {5, 19},
  {2, 5, 19},
  {3, 5, 19},
  {2, 3, 5, 19},
  {23},
  {2, 23},
  {3, 23},
  {2, 3, 23},
  {29},
  {2, 29},
  {3, 29},
  {2, 3, 29},
  {31},
  {2, 31},
  {3, 31},
  {2, 3, 31},
  {37},
  {2, 37},
  {3, 37},
  {2, 3, 37},
  {41},
  {2, 41},
  {3, 41},
  {2, 3, 41},
  {43},
  {2, 43},
  {3, 43},
  {2, 3, 43}]

def termCoeff : Fin 72 → ℤ := ![1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1]

noncomputable def certificate : SievePolynomial where
  Term := Fin 72
  fintypeTerm := inferInstance
  primes := termPrimes
  coefficient := fun a => (termCoeff a : ℝ)

lemma term_primes_prime (a : Fin 72) : ∀ p ∈ termPrimes a, p.Prime := by
  fin_cases a <;> norm_num [termPrimes]

lemma certificate_supported : certificate.SupportedOn primes := by
  intro a
  fin_cases a <;> decide +kernel

end Erdos970.Rounded600
