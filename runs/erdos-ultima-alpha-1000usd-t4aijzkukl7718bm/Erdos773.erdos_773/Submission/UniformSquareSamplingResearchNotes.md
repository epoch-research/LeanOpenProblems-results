# Uniform Gaussian degree bounds and sharp-density sampling

The original conjecture is NOT settled. Spec.lean is unchanged, with its
sole admission for 0<epsilon<=1/3. No proof submission has been made.
A subsequent completed application, recorded in UntrimmedSquareLowerResearchNotes.md,
now proves the actual lower bound N^(2/3)/36 eventually.

## Completed uniform incident-degree bound

GaussianIncidentDegree.finite_degree_bound proves, for 1<=a<=N,

    degree(edges [1,N],a) <= N*((83/250)*log(2N)+28006).

GaussianIncidentDegree.eventual_degree_bound proves uniformly in a,

    eventually degree(edges [1,N],a) <= (333/1000)*N*log N.

All finite factor witnesses, multiplicities, residue fibers, sieve weights,
radial sums, axis terms, square-root cutoffs, and rounding are accounted for.
Details are in GaussianIncidentDegreeResearchNotes.md.

## Completed uniform sampling theorem

UniformSquareSampling.logarithmic_sampling proves that for every fixed
0<delta<1, eventually there is an actual B subset [1,N] with

    |B| >= (1-delta)*N/log N,
    square values of B are ThreeAPFree,
    degree(edges B,a) < (1999/6000)*N/(log N)^2 for every a in [1,N].

The coefficient 1999/6000 is strictly below 1/3. There is NO maximum-degree
trimming loss. The sampled set is NOT asserted to be Sidon. There is no
upper bound |B|<=N/log N; the theorem supplies only |B|<=N by containment.

## Finite high-moment mechanism

HypergraphSamplingMoments proves for an r-uniform H with D edges and
maximum vertex degree K, and Bernoulli vertex sampling with density p,

    E[X^q] <= (p^r*D+r*q*K)^q.

This is the actual finite Bernoulli expectation, not a conditional moment
assumption. The proof recursively sums ordered edge tuples, weighted by
p^(card of their union). At each step, at most |U|K edges meet the prior
union U; the others incur p^r. Since |U|<=rq, induction proves the bound.
A finite Markov tail bound is also proved.

UniformDegreeSampling selects a maximum of the penalized reward

    sampled_card - sampled_progression_count
      - V*sum_b (sampled_link_count_b/T)^q.

Its expected value is bounded from below by the preceding moments. If a
link count is >=T, the penalty is at least V, so a strictly positive reward
cannot violate any cap. Deleting progression supports then preserves all
caps and the lower cardinality bound. This avoids an extra cardinality
concentration lemma.

UniformHypergraphSampling supplies exact link-card and link-degree
identities/inequalities. A four-edge link is three-uniform, and its maximum
vertex degree is bounded by the original pair codegree. Erasing the center
is injective on its incident edges; the center itself has link degree zero.
UniformAmbientSampling transports the theorem to an arbitrary finite carrier
by subtypes, with exact cardinality and induced-hypergraph transport.

## Instantiated scales

Put X=N, L=log N,

    p=1/L,
    D=(333/1000)*X*L,
    T=(1999/6000)*X/L^2,
    q=K=ceil(X^(1/100)).

The original pair-codegree estimate eventually gives codegrees <=K.
For 16000*L<=X^(1/100), the exact scalar estimates prove

    3*q^2*L^2 <= X/12000,
    (p^3*D+3*q*K)/T <= 3999/4000,
    (3999/4000)^q <= X^-4.

Thus the union-bound penalty V^2 times the moment ratio is <=X^-2.
The progression count is <=24*X*L, and total sampling/deletion loss is
<=25*X/L^2. The conditions L>=25/delta and L>=2 yield the stated size.
All logarithmic hypotheses are obtained from the standard little-o bound
log X=o(X^(1/100)). No numerical sampling or unverified asymptotics is used.

## Clean modules and audit

New completed modules after the earlier Gaussian normalization:

- GaussianIncidentEncoding.lean
- GaussianIncidentCounting.lean
- GaussianDirectionWeights.lean
- GaussianRadialBins.lean
- GaussianRadialCounting.lean
- GaussianDirectionSum.lean
- GaussianIncidentDegree.lean
- HypergraphSamplingMoments.lean
- UniformDegreeSampling.lean
- UniformHypergraphSampling.lean
- UniformAmbientSampling.lean
- UniformSquareSamplingScales.lean
- UniformSquareSampling.lean

All compile cleanly and have built oleans. GaussianSamplingAudit.lean checks
40 declarations, all with only propext, Classical.choice, Quot.sound, and no
warnings. Log: /tmp/gaussian-sampling-combined-audit.log.

Individual logs are /tmp/<hyphenated-module-name>.log, e.g.
/tmp/hypergraph-sampling-moments.log, /tmp/uniform-square-sampling.log.
The temporary GaussianCountCheck.lean was removed.

Final main-file check: /tmp/spec-gaussian-sampling-check.log. Its known
admission remains; SHA-256 is
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.

## Remaining mathematical gap

This removes the degree-trimming obstacle, but not the conservative
long-time greedy envelope. The subsequent UntrimmedSquareLower module applies the current relaxed
extraction and proves the numerical N^(2/3) coefficient 1/36; this does not
settle even the coefficient-one endpoint.
A genuinely sharp long-time profile theorem is still missing. A proof of
that endpoint would still leave every 0<epsilon<1/3 unresolved. No new
exponent argument or fixed-power disproof is presently available.
