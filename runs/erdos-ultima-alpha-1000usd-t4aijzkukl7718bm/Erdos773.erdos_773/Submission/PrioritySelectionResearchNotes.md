# Random-priority extraction and an improved actual Sidon lower constant

This is NOT a settlement of Erdős 773. The original conjecture in Spec.lean
is unchanged, with its sole admission for 0 < epsilon <= 1/3. No proof was
submitted. The exponent remains 2/3 and the logarithmic loss remains.

## New actual lower bound

`PrioritySquareSidonLower.eventual_log_lower` proves

    eventually M(N) >= (5/4) N / (N log N)^(1/3),

where M(N) is exactly the maximum in the original conjecture. This improves
the previously proved coefficient 1. It does NOT prove epsilon=1/3, because
(log N)^(-1/3) tends to zero, nor does it improve the exponent.

Five new modules are fully compiled and built. None imports admitted Spec.
All twenty-one printed main audits use only propext, Classical.choice,
Quot.sound. The combined final log is

    /tmp/priority-selection-final-audit.log

## 1. ProductCorrelation.lean

This packages Mathlib's full weighted FKG theorem (in
Combinatorics/SetFamily/FourFunctions.lean), not merely the unweighted
Harris-Kleitman special case.

For a finite distributive lattice with normalized nonnegative log-supermodular
mass mu and nonnegative increasing functions F_i,

    product_i E_mu[F_i] <= E_mu[product_i F_i].

For a finite product of chains, `weight W x = product_i W_i(x_i)` is
log-MODULAR, even if some W_i vanish. At each coordinate min and max just
permute two values. Normalized marginals therefore give the needed FKG mass.

`sum_weight_restrict` computes the probability of coordinatewise restrictions.
`pin W v t` fixes coordinate v=t while retaining the other marginal masses.
`weight_pin`, `weight_mixture`, and `expectation_mixture` rigorously justify
conditioning and the mixture over the pinned priority. Zero-probability
configurations are handled explicitly; there is no division by their masses.

## 2. PriorityHypergraphSelection.lean

Assign each vertex an independent uniform priority in Fin K, K>0.
`survivors H x` retains a vertex iff every incident edge has another vertex
of STRICTLY higher priority. Ties are rejected. Thus no nonempty edge can
be contained in the survivor set: a maximal-priority vertex of that edge
would be rejected.

Conditioned on rank(v)=t, an incident edge e fails to block v with probability

    1 - ((t+1)/K)^(|e|-1).

These failure events are increasing functions of the other priorities.
FKG therefore supplies their product as a LOWER bound on simultaneous
survival, regardless of overlaps among the links. The finite theorem gives
an actual independent set B with

    |B| >= sum_v (1/K) sum_{t=0}^{K-1}
                 product_{e containing v} [1-((t+1)/K)^(|e|-1)].

No linearity, bounded codegree, or degree regularity is assumed. Empty edges
are explicitly excluded. Singleton edges give a zero survival factor.

## 3. PriorityIntegralSelection.lean

For an antitone f on [0,1] with f(0)<=1 and f(1)>=0,

    integral_0^1 f <= (1/K) sum_{t=0}^{K-1} f((t+1)/K) + 1/K.

This follows from Mathlib's monotone sum/integral comparison after rescaling
the interval to [0,K]. The difference between left and right sums telescopes.
No Riemann-sum convergence theorem is needed.

Choose one maximum independent set BEFORE varying K. Each finite priority
bound is at most its size. Summing the error over all vertices gives n/K;
letting K grow via the Archimedean property proves

    alpha(H) >= sum_v integral_0^1
                         product_{e containing v} (1-x^(|e|-1)) dx.

For an (r+1)-uniform hypergraph this is the Caro--Tuza integral bound

    alpha(H) >= sum_v integral_0^1 (1-x^r)^degree(v) dx.

Again this is NOT the sparse-hypergraph logarithmic-gain theorem.

## 4. CaroTuzaFourUniform.lean

Put C(d) = integral_0^1 (1-x^3)^d dx. The file proves C(d)>0, C(0)=1, and

    (3d+4) C(d+1) = (3d+3) C(d).

The recurrence is obtained by integrating the derivative of
x(1-x^3)^(d+1); it does not assume a Gamma-function evaluation.
A polynomial induction then gives

    C(d)^3 (3d+2) >= 2.

The key recurrence comparison is the nonnegative polynomial difference

    (3d+3)^3(3d+5) - (3d+2)(3d+4)^3 = 6d+7.

`inverse_cube_sum` proves the necessary power-mean inequality directly.
For positive C_i with C_i^3 D_i>=1,

    n^4 <= (sum_i C_i)^3 sum_i D_i.

Its tangent inequality is 4m <= D_i m^4+3C_i, derived by expanding
(C_i-m)^2(3C_i^2+2C_i m+m^2)>=0. Taking m=(sum C_i)/n finishes, with the
empty ambient set handled separately.

Since sum_v degree(v)=4E, take D_v=(3degree(v)+2)/2. The final theorem gives
an actual independent set B in ANY four-uniform hypergraph with n vertices
and E edges such that

    n^4 <= |B|^3 (6E+n).

`finite_selection` transfers this to an arbitrary ambient finset A, with
B subset A and every forbidden edge avoided. The subtype-edge image cannot
increase the edge count, and preserves the size of each contained edge.

## 5. PrioritySquareSidonLower.lean

`sidon_of_edge_avoidance` proves that avoiding four-root edges inside a
progression-free square carrier really gives Sidon square values. All
nontrivial collisions there have four distinct roots by the earlier
APFreeExtraction lemma; no three-root obstruction is dropped.

`carrier_bound`: for A subset [1,N] whose square values are ThreeAPFree,

    |A|^4 <= M(N)^3 (6 E4(A)+|A|).

The controlled logarithmic sampler at delta=1/2000 gives eventually

    (1999/2000) N/log N <= |A| <= N/log N,
    E4(A) <= (33/400) N^2/(log N)^3.

Use also 1000(log N)^2<=N, eventually by
Real.isLittleO_pow_log_id_atTop with exponent two.
Writing X=N, L=log N, the denominator satisfies

    (6 E4(A)+|A|) L^3 <= (62/125) X^2.

The fourth power of the carrier lower bound and the rational comparison

    (62/125)(125/64) <= (1999/2000)^4

then prove (125/64)X^2 <= M(N)^3 L. Taking the cube comparison with
R=(X L)^(1/3) yields the displayed coefficient 5/4 in the actual lower bound.

## Main file and remaining gap

The main-file compile is /tmp/spec-priority-selection-check.log. Spec.lean
still has its original admission at line 2031, and SHA-256

917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14

No necessary declarations have been consolidated into Spec yet, because
there is still no complete proof or disproof of the conjecture.

A true logarithmic-gain extraction theorem would go beyond the one-step
priority bound just proved, and might establish an endpoint with suitable
constants and hypotheses. Even that would not settle 0<epsilon<1/3.
The arithmetic factorization review produced no stronger root selector.
