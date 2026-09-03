# Stronger genuine-prime metric results — original still unsolved

Spec.lean remains unchanged, with the original sorry. There is no proof or
disproof of the universal assertion, and nothing has been submitted as a
settlement.

## New verified files

### MetricFrequentLinear.lean
Namespace Erdos972MetricFrequentLinear.

Defines richTail(A,B) by existence of N>B with

    widePairs A N alpha > N/16.

These weights count actual prime input/output pairs. From the existing
localized first-moment lower bound and the uniform sieve upper bound outside
small rational neighborhoods, proves

    volume.real ((a,b) intersect richTail(A,B)) >= (b-a)/640000

for 1<a<b<A. The proof subtracts the N/16 threshold on the complement of the
rich tail, then lets the rational-neighborhood error tend to zero. Applying
the existing Lebesgue-differentiation lemma yields

    for almost every alpha, for every natural A>alpha>1 and every B,
    some N>B has widePairs A N alpha > N/16.

No interchange between a scale depending on alpha and an almost-everywhere
quantifier is made. The countably many A,B are combined by ae_all_iff.

### LinearPrefixDivergence.lean
Namespace Erdos972LinearPrefixDivergence.

For a nonnegative sequence a and c>0, if

    for every B some N>B satisfies sum_{1<=n<=N} a(n) > c*N,

then sum a(n)/(n+1) is not summable. Proof: reciprocal summability gives a
finite exceptional prefix and arbitrarily small reciprocal tails. Such tails
bound the remaining unweighted partial sum by epsilon*(N+1), contradicting
the frequent linear lower bound.

### MetricLogDivergence.lean
Namespace Erdos972MetricLogDivergence.

- widePairs_le_primeCorrelation: the bounded-output-ratio weight is at most
  the full genuine-prime correlation, pointwise for every alpha,A,N.
- ae_frequently_linear_primeCorrelation: for almost every alpha>1, every B
  has an N>B with primeCorrelation(alpha,N)>N/16.
- ae_not_summable_prime: for almost every alpha>1, the nonnegative series

      sum 1_{n and floor(alpha*n) prime} log(n)log(floor(alpha*n))/(n+1)

  is not summable.
- ae_logPrimeCorrelation_tendsto: these partial sums tend to +infinity for
  almost every alpha>1.
- ae_not_summable_mangoldt and ae_logMangoldtCorrelation_tendsto: the same
  conclusions for the reciprocal-weighted Mangoldt correlation. They use
  the existing summable proper-prime-power error and pointwise domination.

This is stronger than the existing almost-everywhere infinitude result. It
is NOT a pointwise result for every irrational slope, and it does not prove
an asymptotic or an eventual linear bound at every scale. The divergence rate
of the reciprocal sums is not quantified.

### AuditMetricLogDivergence.lean
All nine principal declarations compile and audit with only propext,
Classical.choice, Quot.sound.

## Remaining gap

The metric, topological, and reciprocal criteria still do not exclude an
individual exceptional irrational slope. No lower bound for the actual
signed four-factor remainder at such a prescribed slope has been found.
Combining almost-everywhere divergence with comeagreness does not remove
this gap.
