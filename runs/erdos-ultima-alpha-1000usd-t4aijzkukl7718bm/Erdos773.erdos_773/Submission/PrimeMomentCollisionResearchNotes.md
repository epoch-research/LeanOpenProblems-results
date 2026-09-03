# Prime and pairwise-coprime growing-moment collisions

This is NOT a settlement of Erdos 773. The original theorem in Spec.lean
remains unchanged, with its sole admission for 0<epsilon<=1/3.

## Main new verified theorem

`PrimeMomentCollisions.lean`, namespace `Erdos773.PrimeMomentCollisions`, proves

    prime_moment_collision_quadratic_log (k : Nat)

There exist four distinct primes a,b,c,d, each at least 5 and strictly below
2^L, where

    L = 2^20 * (k+1)^2 * ((k+1).log2+1)^2,

such that

    a^2+b^2=c^2+d^2,

and their first k positional binary digit moments agree. The moment is
formally defined as

    binaryDigitMoment L n j = sum_{i<L} (if n.testBit i then i^j else 0).

Since all roots are below 2^L, these sums include every binary digit of each
root. Distinct primes are pairwise coprime. This is a genuine prime-root
existence theorem, not a numerical conjecture that some computed roots are
prime. No specific huge prime quadruple is extracted.

The file also proves:

* `eventually_prime_moment_collisions`: for each FIXED k, the same phenomenon
  occurs at every sufficiently large bit length m+1.
* `exists_pairwise_coprime_prime_moment_collision`: packages the pairwise
  coprimality explicitly, together with primality, distinctness, and moments.
* `prime_moment_collision_quartic`: the simpler bound L=(256*(k+1))^4.

The quadratic-log-squared bound is the strongest verified quantitative one.
It improves on the previous O(k^4 log^2 k) primitive construction in both
length and arithmetic scope, although the previous construction is explicit
whereas this one uses counting and the existing upper bound.

## Why the existing upper bound suffices

There are at most (L^k+1)^k <= L^(k(k+1)) colors for the first k moments when
L>=2. Every moment of order j<k is at most L^k.

The elementary prime-count lower bound already proved in PrimorialSquareSieve
supplies at least about 2^m/(8m log 2) primes in [5,2^(m+1)]. The maximum Sidon
subset of squares up to N is at most

    2N exp(-log N/(512 log log N)).

To ensure a FOUR-DISTINCT-root collision, rather than just a repeated-middle
three-root progression, a new constant-fraction weak-Sidon extraction lemma
is used. If the largest moment fiber had no four-distinct-entry collision,
at least a quarter of it would be Sidon. For the displayed L the resulting
lower cardinality exceeds the verified Sidon upper bound.

The numerical entropy criterion, proved in `PrimeColorCollisions.lean`, is

    128 C (m+1) exp(-((m+1)log 2)/(512 log((m+1)log 2))) < 1,

with m>=895, where C is the number of colors. It guarantees a monochromatic
four-distinct-root collision in `sievePrimes (2^m)`.

For the quadratic-log-squared bound, put K=k+1 and ell=log2(K)+1. Then

    log L <= 24 ell,
    log 128 + (k(k+1)+1) log L <= 31 K^2 ell,
    512 log(L log 2) <= 12288 ell,
    L log 2 >= 2^19 K^2 ell^2.

The strict numerical comparison 31*12288 < 2^19 proves the criterion.

## Weak Sidon extraction (new clean module)

`WeakSidonExtraction.lean` defines WeakSidon to mean that equal pair sums
are trivial unless one side repeats its entry. It proves:

    extract
    card_le_four_max

Every finite weak Sidon set A contains a Sidon subset of cardinality at least
|A|/4. The proof counts nontrivial three-term progression supports. Their
centers are injective: two different progressions with the same center would
supply a forbidden four-distinct-entry collision. Thus there are at most |A|
three-vertex supports. Bernoulli alteration with p=1/2 retains at least
|A|/2-|A|/8, in particular |A|/4. Avoidance of the progression supports, together
with the weak Sidon assumption, gives the full Sidon property.

## Prime coloring theorem (new clean module)

`PrimeColorCollisions.lean` proves:

* `four_collision_of_card`: a general finite coloring criterion, with the
  factor four from weak-Sidon extraction.
* `eventually_prime_color_collision`: for each fixed natural r, eventually
  every coloring of primes in [5,2^(m+1)] with at most (m+1)^r colors has a
  monochromatic four-distinct-root square collision. This uses the older
  stretched-exponential upper bound, which already beats every fixed
  polynomial in the bit length.
* `prime_color_collision_of_entropy`: the finite criterion above, using the
  stronger primorial bound.

## Scope and remaining gap

These are obstructions to blanket sufficient conditions based on primality,
pairwise coprimality, and too few binary digit moments. They do NOT show that
every moment class is bad, and do NOT rule out selecting a specially chosen
class or imposing a larger collection of constraints. In particular they
are not a negation of the original N^(1-o(1)) Sidon conjecture. No actual Sidon
exponent improved, and no fixed-power upper bound on the maximum was proved.

## Verification

All three new modules compile without warnings or admissions. Their printed
axiom audits contain only

    propext, Classical.choice, Quot.sound.

Logs:

    /tmp/weak-sidon-extraction-final.log
    /tmp/prime-color-collisions-final.log
    /tmp/prime-moment-collisions-final.log

The corresponding .olean files are in `.lake/build/lib/lean/Submission/`.
No admitted Spec theorem is used. The main-file check is
`/tmp/spec-prime-moment-check.log` and still reports the expected sorry.

A kernel recursion problem in an intermediate draft was resolved by proving
the bit-length transport helper with abstract length parameters, rather than
expanding a large dependent cast at its application. The final theorem is
accepted by the ordinary kernel and has the clean audit above. Temporary
debug sources were removed. No proof submission was made.
