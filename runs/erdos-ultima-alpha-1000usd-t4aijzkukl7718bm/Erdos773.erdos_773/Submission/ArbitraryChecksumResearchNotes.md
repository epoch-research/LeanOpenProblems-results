# Arbitrary finite checksum selectors: positive examples

This continuation does NOT settle Erdős 773. Spec.lean is unchanged with its
sole sorry at line 2031 for 0 < epsilon <= 1/3. No proof was submitted.

## Three new fully checked modules

* SidonPairCertificate.lean
* CubicChecksumExample.lean
* FiveChecksumExample.lean

All have built oleans, no admissions or warnings, and 15 printed main audits
using only propext, Classical.choice, Quot.sound (some use fewer axioms).
None imports Spec.lean.

## A cubic checksum at q=3

For r=0,...,26, write r=x+3y+9z and put

 f(x,y,z) = 1 + z^2 + y + x + 2xz^2 + 2xy + 2xyz + 2xy^2
              + 2x^2 + 2x^2z  (mod 3),
 n_r = r+27 f(x,y,z).

The 27 resulting roots are positive, at most 80, and occupy distinct residues
modulo 27. Their square values are Sidon. The verified table is

 [4,6,7,10,11,12,16,21,25,27,28,35,40,41,42,44,50,51,56,57,59,63,72,73,74,76,80]

in sorted order. The root_formula theorem separately verifies the cubic
formula against the table indexed by the residue r.

This complements the earlier negative finite checks for affine/quadratic
checksums. No minimal-degree assertion is made in Lean.

The positive-coefficient polynomial is NOT a uniform rule in q: replacing
3 by 5 in its modulus yields roots 125,278,253,170 with

    125^2+278^2 = 253^2+170^2 = 92909.

cubic_rule_fails_at_five proves the resulting non-Sidon statement in Lean.
It does not rule out other cubic rules or other uniform constructions.

## An arbitrary checksum at q=5

FiveChecksumExample defines an explicit 125-entry root table. It proves:

* exactly 125 distinct roots;
* every root lies in [1,624];
* root(r) mod 125 = (r+1) mod 125, for r:Fin 125;
* root(r)=r+1+125*checksum(r), with 0<=checksum(r)<5;
* the entire square-value set is Sidon.

The checksum is a finite lookup function, not a formula claimed to work at
other primes. The 125 roots have 7875 distinct unordered square sums,
including repeated summands. The checked finite lower bound is M(624)>=125.
The cubic module likewise proves M(80)>=27.

Thus both finite instances meet the q^3-at-height-q^4 target. This is NOT
an asymptotic N^(3/4) lower bound: no family for unbounded q, no tensor or
concatenation preservation theorem, and no exponent-improving amplification
has been obtained.

## Kernel-verifiable certificate

SidonPairCertificate.squares_sidon is a general theorem. Given f:Fin m->Nat,
a list L of pairs (i,j) with i<=j, with length at least the cardinality of all
ordered-index unordered pairs, and with the square sums strictly increasing
along L, the square values of f are Sidon.

Strict increase gives nodup of the sum list and hence of L. Containment and
cardinality show L covers all unordered pairs. Injectivity of the sum map
then gives the usual unordered-pair matching. This is proved abstractly.

Each example supplies a literal list of pairs sorted by its square sums.
The lists have respectively 378 and 7875 entries. All finite certificates
use decide +kernel, not native_decide and not solver trust.

Important performance detail: for the 7875-entry list, proving
`forall p in L, ...` directly by decide can choose the finite-type forall
instance and scan all 15625 possible pairs, doing expensive membership tests.
The successful proof instead checks the linear Boolean `List.all` expression,
then uses List.all_eq_true to obtain the bounded universal statement.
The 125-root module takes about two minutes to check in this environment.

## Exploratory search and reproducibility

Research/ArbitraryChecksumSearch.py builds exact forbidden supports and uses
SciPy/HiGHS for a finite MILP. It found the unrestricted q=3 example quickly;
the q=5 run timed out with no incumbent after 180 seconds. A timeout is NOT
an infeasibility result.

Research/PolynomialChecksumSearch.py found the displayed cubic at q=3.
A later coefficient-minimization run timed out without a new witness. No
optimality claim follows from that run.

Research/ChecksumWalk.cpp performs exact-integer local CSP search. At q=5
it found the 125-root table after 2,782,178 moves. A separate Python check
validated all 7875 unordered sums, and the subsequent Lean certificate
established the theorem independently of either program.

Data and logs:
    /tmp/polynomial-checksum-3-3.json
    /tmp/arbitrary-checksum-5-walk.json
    /tmp/checksum-walk-5.in
    /tmp/checksum-walk-5.out
    /tmp/checksum-walk-5.log
    /tmp/sidon-pair-certificate.log
    /tmp/cubic-checksum-final.log
    /tmp/five-checksum-final.log

The source files contain the full checked tables and certificates, so no
external JSON file or solver is needed to verify the Lean results.

## Original problem status

The separate review of residue-fiber amplification did not produce a
subpower-loss cross-difference selector. A direct-IP attempt to access the
problem reference timed out; no external mathematical result was obtained.

No original-conjecture asymptotic exponent improved. The strongest completed
actual asymptotic lower bound remains eventual M(N)>=N^(2/3)/500. The upper
bounds remain compatible with N^(1-o(1)). Spec.lean SHA-256 is unchanged:

917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
