# Uniform horizon ceiling for the existing greedy certificate

The original conjecture remains UNSETTLED. Spec.lean is unchanged, with its
sole admission for 0 < epsilon < 1/3. Its completed unconditional endpoint
remains eventual M(N) >= N^(2/3). No incomplete proof has been submitted.

## New verified module

`GreedyBatchHorizonCeiling.lean` imports the clean
`GreedyBatchSquareScales` module, not the admitted `Spec.lean`. It builds
without warnings or admissions. All seven printed axiom audits use only
propext, Classical.choice, and Quot.sound.

Log: `/tmp/greedy-batch-horizon-ceiling.log`.
Olean: `.lake/build/lib/lean/Submission/GreedyBatchHorizonCeiling.olean`.
Namespace: `Erdos773.GreedyBatchHorizonCeiling`.

## Exact terminal budget

For the existing coefficient

    a(m) = 1 - 1000/m^2,

`terminal_log_budget` proves that the certificate condition

    m^1000 <= d exp(-a(m) ((T+1)^3-1))

implies

    a(m) ((T+1)^3-1) + 1000 log(m) <= log(d).

For m>=100, `a_lower` gives a(m)>=1/2. Hence, when T>=0,

    T^3 <= 2 log(d).

This is `horizon_cube_le_two_log`. With d<=X^K and X>0,
`polynomial_horizon_cube` gives T^3<=2K log(X).

## Uniform asymptotic statements

For each fixed K>0 and delta>0, `eventually_subpower_horizon` gives,
UNIFORMLY over all eligible m,d,T at each sufficiently large N,

    T <= N^delta.

It assumes m>=100, d>0, T>=1, d<=N^K, and the terminal condition.
There is no fixed choice of m or T hidden before the eventual quantifier.

For every real gamma, with the additional lower bound N^gamma<=d,
`eventually_output_ceiling` bounds the numerical output

    efficiency(m) (T-1) V/d <= N^(1-gamma+delta),

for all m>=2000000, 0<=V<=N, and eligible d,T. The proof uses
`efficiency_bounds`, the uniform horizon bound, and rpow identities.

## Specialization to the completed endpoint's degree scale

The existing degree scale is

    scale(N) = (kappa N/(log N)^2)^(1/3),
    kappa = 1999/6000.

`eventually_scale_lower` proves scale(N)>=N^(1/3-eta) eventually for EVERY
eta>0, rather than only the endpoint module's fixed small slack.

The main new result, `eventually_endpoint_no_power_gain`, states: for every
delta>0, eventually in N, for EVERY m,T,V satisfying

    m>=2000000, T>=1, 0<=V<=N,
    m^1000 <= scale(N) exp(-a(m) ((T+1)^3-1)),

one has the STRICT bound

    efficiency(m) (T-1) V/scale(N) < N^(2/3+delta).

Thus merely changing m or T in the existing certificate, while retaining
this degree scale, cannot certify a fixed exponent above two thirds, even
if the numerical carrier size V is allowed to be all N roots.

## Scope

These are upper bounds on a particular certificate's NUMERICAL LOWER BOUND.
They are NOT upper bounds on the actual maximum Sidon cardinality M(N),
and do not constitute an original-conjecture disproof. They do not rule
out a stronger certificate, a better arithmetic carrier with lower degree,
or a different near-linear construction. No exponent improvement or
near-linear selector was found in this continuation.

The scale-dependent amplification route was also reviewed. Its established
conditional equivalence remains unproved; neither the full-fiber bounds
nor the constant-loss amplification obstruction applies to every sparse,
scale-dependent construction. No valid new amplification theorem emerged.

## Main file

Original theorem: line 17276.
Sole admission: line 17287.
Sole import unchanged: `import FormalConjecturesUtil`.
SHA-256:

    257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940
