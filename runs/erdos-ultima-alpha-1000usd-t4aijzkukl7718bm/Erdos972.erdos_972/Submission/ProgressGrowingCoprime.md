# Growing-modulus prime-input estimate — conjecture remains unsolved

`Submission/Spec.lean` is unchanged and still contains the original `sorry`.
There is no completed proof or irrational counterexample. Do not submit this
partial development as a settlement.

## Newly completed and audited

`Submission/GrowingCoprimeCandidates.lean`
Namespace: `Erdos972GrowingCoprimeCandidates`.

The file compiles without errors or warnings. Its principal theorem depends
only on `propext`, `Classical.choice`, and `Quot.sound`.

For alpha > 1 irrational and every B, it proves that there is u > B with
v = root64(u) >= 2048 such that, for every integer 0 < D <= v,

    sum_{0 < p <= u^6, p prime, gcd(floor(alpha*p), D)=1} log p
        >= u^6 / (8 D).

The same u works for all these D. The sets of input primes may differ with D;
the theorem does NOT provide a single input avoiding all D <= v.

The proof uses direct rational approximants to alpha, the established
scaled prime-rotation estimates, qualitative Chebyshev PNT, and the explicit
prime-power error O(sqrt(N)). These scales have N = u^6. They are not
identified with the reciprocal-alpha scales N = floor(u^6/alpha) in the
centered four-factor reduction.

Supporting lemmas:
- `arc_le_coprimePrimeWeight_add_prime_powers`
- `coprime_arc`
- `coprime_arc_margins`
- `coprimePrimeWeight_lower_of_arc`
- `sixth_scale_primePower_tendsto`
- `eventually_coprime_prime_budget`

Compilation:

    lake env lean -o .lake/build/lib/lean/Submission/GrowingCoprimeCandidates.olean \
      Submission/GrowingCoprimeCandidates.lean

## Exact limitation

To use this bound for an output with no prime divisor up to R, one can take
D = R! (when R! <= v), or a product of small primes. This sifts far below the
square-root cutoff needed to infer primality of an output of size alpha*u^6.
The already verified exact criterion is in `SieveBarrier.lean`.

It is invalid to conclude that these coprime outputs are prime, or to exchange
the quantifiers on D and the input prime. The theorem is not a lower bound for
prime pairs, nor for the two-Mangoldt correlation.

## Mathematical review in this continuation

No new sufficient lower bound or counterexample was found.

- Reconsidered binary Fourier estimates: the established one-prime minor-arc
  bounds with a direct L2/Cauchy-Schwarz argument do not control the signed
  two-prime minor-arc contribution at the main-term scale. No improvement
  supplying the needed lower bound was established.
- Reconsidered rational approximants and lattice coordinates: the transformed
  region stays thin and its coefficients grow. A prime linear-forms theorem
  for fixed coefficients on large boxes cannot be inserted without uniform
  error control in that region.
- Reconsidered a nonnegative sieve majorant: its level of distribution and
  mean must be justified. No mean-2 majorant with the necessary mixed
  correlation estimates was supplied, and no secondary-term gain was proved.

The actual sufficient targets remain those recorded in
`ProgressFourFactor.md` and `ProgressSublinearCriterion.md`. Their lower-bound
hypotheses remain unproved. Further work should focus on that gap, rather
than re-deriving fixed-modulus coprimality or more equivalent criteria.
