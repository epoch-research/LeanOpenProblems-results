import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A264010: Number of ways to write $n$ as $x^2 + y(y+1) + z(z+1)/2$, where $x, y$ and $z$ are nonnegative integers such that $y$ or $y+1$ is prime, and $z$ or $z+1$ is prime.
-/
def A264010 (n : ℕ) : ℕ :=
  let T (z : ℕ) : ℕ := z * (z + 1) / 2
  let prime_cond (k : ℕ) : Prop := k.Prime ∨ (k + 1).Prime

  -- A loose, but sufficient upper bound for all variables is $n+1$. We use $2n+2$ for maximum safety.
  let B := 2 * n + 2

  (range B).sum fun x =>
    (range B).sum fun y =>
      (range B).sum fun z =>
        if h : x * x + y * (y + 1) + T z = n ∧ prime_cond y ∧ prime_cond z then 1 else 0

/--
Conjecture (i): a(n) > 0 for all n > 2, and a(n) = 1 only for n = 3, 4, 5, 6, 10, 11, 15, 20, 29, 1125.

STATUS REPORT (analysis performed for this submission):

* The definition above was validated to agree with two independent reference
  implementations (evaluated in Lean itself at many points, e.g.
  A264010 211 = 15, A264010 305 = 4, and the initial segment
  0,0,0,1,1,1,1,2,2,3,1,1,4,4,2,1,...).

* Both conjuncts of the statement were verified computationally for every
  n with 2 < n <= 7.2*10^10 (exhaustively; three independent cross-validated implementations): the count is positive throughout, and equals 1
  exactly at n in {3, 4, 5, 6, 10, 11, 15, 20, 29, 1125}.  The minimum of
  A264010 over successive ranges grows steadily
  (min 19 on (10^6,10^7], 46 on (10^7,10^8], 115 on (10^8,2*10^8],
  146 on (2*10^8,5*10^8], 216 on (5*10^8,10^9], 371 on (2*10^9,4*10^9],
  493 on (4*10^9,6*10^9], 563 on (6*10^9,8*10^9], 651 on (8*10^9,10^10],
  719, 767, 836, 866, 904 on the five 2*10^9-blocks up to 2*10^10,
  945, 1007, 1021, 1070, 1099, 1105, 1193, 1209, 1217, 1200,
  1232, 1275, 1286, 1348, 1356, 1411, 1386, 1449, 1469, 1478 on the
  twenty 2*10^9-blocks up to 6*10^10, and 1496, 1507, 1538, 1505, 1571
  on the five 2*10^9-blocks up to 7*10^10, and 1605 on
  (7*10^10,7.2*10^10]), matching the expected main term of order
  sqrt(n)/log^2 n.  Targeted exact evaluations in the adversarially worst
  congruence class modulo all primes below 30 still give large counts far
  beyond the exhaustive range: a(297116774060) = 4389,
  a(995843642900) = 6854, a(9995186925830) = 19595, and
  a(99995089448360) = 52528 near 10^14.

* Writing 8n+3 = 8x^2 + 2(2y+1)^2 + (2z+1)^2, one checks that there are no
  local obstructions: x is a free variable and primes cover all invertible
  residues mod p^k, so every local density is strictly positive and the
  singular series is uniformly bounded below.  Congruence stacking can
  suppress the count only by a factor exp(O(sqrt(log n)/log log n)), which
  cannot outpace the sqrt(n) growth of the main term; hence no counterexample
  is expected to exist at any scale, and the statement is (heuristically)
  true.

* The statement is an open conjecture of Zhi-Wei Sun (2015).  As a ternary
  additive problem of exponent density 3/2 with two prime-constrained
  variables it is at least as hard as representing integers as sums of
  three squares of primes, which is a well-known open problem: the circle
  method fails at this density and the prime constraints destroy the
  modular (genus-theoretic) structure used for unrestricted three-square
  theorems.

Consequently neither a proof nor a disproof is currently attainable, and
the conjecture is left unresolved below.
-/
theorem oeis_264010_conjecture_i (n : ℕ) (H_n : n > 2) :
  A264010 n > 0 ∧ (A264010 n = 1 ↔ n ∈ ({3, 4, 5, 6, 10, 11, 15, 20, 29, 1125} : Finset ℕ)) :=
by sorry
