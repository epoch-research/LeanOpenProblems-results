# Exact prime-remainder profile identity — still no settlement

The original conjecture is STILL UNSOLVED. Spec.lean is unchanged and retains
its original sorry. No sufficient signed lower bound or irrational
counterexample was found. No proof was submitted.

## Verified addition: PrimeRemainderProfileIdentity.lean

Namespace Erdos972PrimeRemainderProfileIdentity. All principal declarations
compile and audit with only propext, Classical.choice, Quot.sound.

Write a_U = mu_{>U} * zeta, and let delta_1 denote the Dirichlet identity.

- `truncated_moebius_prime_invariant`: for p prime, p>U, and every n,

  (mu_{<=U} * zeta)(n*p) = (mu_{<=U} * zeta)(n).

  Proof uses preservation of divisibility by every d<=U under multiplication
  by p. It also handles n=0.

- `divisorCoeff_mul_large_prime`: the CORRECT identity for a_U is

  a_U(n*p) = a_U(n) - delta_1(n).

  Thus a_U is invariant only away from the unit argument. In particular,
  `divisorCoeff_prime` gives a_U(p)=-1 when U>=1 and p>U.

- `largePrimeLog V` is the arithmetic function zeta*primeMangoldt_{>V}.
  It is the sum of log p over DISTINCT prime divisors p>V, and satisfies
  0<=largePrimeLog(V,n)<=log n.

- `prime_remainder_profile_identity`: for U<=V and EVERY n,

  primeTypeIIPart(U,V,n)
    = a_U(n)*largePrimeLog(V,n) + primeMangoldt_{>V}(n).

  The prime correction is exact and essential. On a prime argument it
  cancels the negative profile term, as the true remainder vanishes there.

- `primeRemainderProfile U V n` denotes a_U(n)*largePrimeLog(V,n).
- `prime_remainder_profile_pair_identity` expands the pair correlation into
  the profile-profile term, two mixed profile-prime terms, and the
  prime-prime correction.
- `prime_pairSum_eq_primeCorrelation` identifies the untruncated prime sum
  with the previous primeCorrelation definition.
- `tail_prime_pairSum_eq`: for alpha>=1 and V<=N, the correction is EXACTLY

  pairSum(alpha,N,primeMangoldt_{>V},primeMangoldt_{>V})
    = primeCorrelation(alpha,N)-primeCorrelation(alpha,V).

  Because floor(alpha*n)>=n, no second cutoff correction is needed above V.

- `offDiagonal_profile_identity` combines this with the already proved
  diagonal splitting. The primeFactorOffDiagonal equals the three profile
  sums plus the ORIGINAL primeCorrelation(alpha,N)-primeCorrelation(alpha,V),
  minus the prime diagonal.

## Consequence and limitations

Pulling a_U through the large prime factors does not on its own establish
signed cancellation. The unit correction restores precisely the original
prime-pair term. Dropping it would be an invalid proof. The identity is not
a theorem that every conceivable use of this representation must fail;
it identifies the missing term in this particular proposed shortcut.

No new conditional criterion was added. The signed off-diagonal bound
required by the common-scale reduction remains unproved.

Other directions reviewed informally in this continuation—large-sieve
factor dispersion, cutoff averaging, metric-to-pointwise transfer, and
bounded-multiplicative parity weights—did not yield a sufficient estimate.
No new theorem from any of those investigations is claimed here.
