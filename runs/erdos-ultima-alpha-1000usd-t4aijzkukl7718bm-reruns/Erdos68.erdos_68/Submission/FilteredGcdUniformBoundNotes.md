# Uniform filtered gcd bounds and raw-boundary denominator divisibility

Verified auxiliary progress, NOT a proof or disproof of Erdős 68.
`Submission/Spec.lean` is unchanged and retains its original `sorry`.

Four new files compile without warnings and have built oleans:

* `FilteredGcdPolynomialBound.lean`
* `FilteredPredecessorUnits.lean`
* `FilteredGcdUniformBound.lean`
* `LambertBoundaryDenominatorLower.lean`

Their printed principal axiom audits use only `propext`, `Classical.choice`,
and `Quot.sound`. No numerical experiment is used in these proofs.

## Sharper residue-one progression

For a prime p, let B=p^(r+1), and suppose every filter degree satisfies
2<=k<B. Then the actual filtered Lambert coefficient satisfies

    b_(B*t+1) = 1 (mod p)     for every t>0.

This is `FilteredPredecessorUnits.filtered_at_pow_pred`.
Pascal's identity writes choose(B*t+1,k) as the sum of two binomial
coefficients with top B*t and lower indices strictly between zero and B.
The earlier Lucas divisibility lemma applies to both. Thus all filters
preserve the original coefficient, and the original predecessor congruence
makes that coefficient one modulo p.

The degree lower bound TWO matters. This progression is shorter than the
previous `FilteredPeriodicUnits` progression, which allowed degree one.
At t=0 the original coefficient is zero, so t>0 is not optional.

## Exact factorial valuation in an aligned block

Lucas gives choose(p^r*t+s,s)=1 modulo p when s<p^r. Factoring the binomial
coefficient then proves

    v_p((p^r*t+s)!) = v_p((p^r*t)!)+v_p(s!).

Consequently, for B=p^(r+1), s<B,

    v_p((B*t+s+1)!/(B*t+1)!) = v_p(B*t+s+1)+v_p(s!).

These are `factorial_valuation_pow_block` and
`factorial_quotient_valuation_eq`. The factor B*t+1 is a p-unit.

## Window valuation bound independent of its endpoint

Retain the earlier exact definition

    G(H,N)=gcd(N!, gcd_(H<=k<=N) [abs(b_k)*N!/k!]).

For H>=2 and H+B<=N, choose

    t=floor((N-1)/B), s=(N-1) mod B, u=B*t+1.

Then t>0, u is in the window, b_u is a p-unit, and the exact block valuation
above gives

    v_p(G(H,N)) <= v_p(N)+v_p((B-1)!)
                 <= v_p(N)+(B-1)/(p-1).

The last division is natural division. These are
`filtered_window_valuation_bound` and `filtered_window_valuation_bound_div`.
Unlike the preceding logarithmic estimate, the extra term beyond v_p(N)
is independent of N.

## Whole-gcd uniform bound

Suppose all filter degrees are in [2,K], H>=2, N>=2H, and

    H+K*(K+1)<=N.

For each prime p<=K choose B=p^ceil(log_p(K+1)). Then

    K<B<=p*(K+1)<=K*(K+1),
    (B-1)/(p-1)<=2*(K+1).

Primes p>K are covered by the earlier large-prime valuation theorem. Hence

    G(H,N) divides N*primorial(K)^(2*(K+1)),
    G(H,N) <= N*16^(K*(K+1)).

The second inequality uses Mathlib's primorial(K)<=4^K. Both results are
uniform in K, not merely eventual statements for each fixed filter.
Principal names are `filtered_window_gcd_dvd_primorial` and
`filtered_window_gcd_le` in `FilteredGcdUniformBound`.

## Exact common-denominator interpretation

`FilteredGcdPolynomialBound` defines

    C(H,N)=N!/G(H,N)

and proves positivity, C*G=N!, and the exact equivalence

    C(H,N) divides D
      iff D*b_k/k! is integral for every H<=k<=N.

Thus C really is the minimal common natural clearing multiplier for the
INDIVIDUAL coefficients in the window. It is not the reduced denominator
of their sum or of a selected weighted sum.

The stronger uniform result gives

    (N-1)! divides primorial(K)^(2*(K+1))*C(H,N).

The earlier polynomial-in-N bound in `FilteredGcdPolynomialBound` is also
verified, but is superseded quantitatively by the uniform primorial bound.
That file remains useful for the exact common-denominator lemmas.

## Connection to the actual raw Lambert boundaries

Let ds be the filter list, M=ds.sum, P=product_(k in ds) k!, and B_n the
existing `LambertBoundaryClearing.boundary ds n`. The new file
`LambertBoundaryDenominatorLower` verifies the exact identity

    (n+1+M)! * (B_(n+1)-B_n) = P*b_(n+1+M).

This uses the previously verified normalized filter identity and the raw
operator's translation and subtraction identities. It is not a statement
about comparison coefficients.

If M<H and D clears every boundary at unshifted indices

    H-M-1 <= n <= N-M,

then adjacent differences show C(H,N) divides D*P. Under the uniform-window
hypotheses above this yields

    (N-1)! divides primorial(K)^(2*(K+1))*D*P.

The main theorem is `factorial_pred_dvd_boundary_multiplier`. Notice the
shift M in both window endpoints. H,N here are factorial coefficient indices.

## Scope and unresolved issue

This supplies a LOWER divisibility bound on simultaneous boundary clearing.
It does not give the small UPPER clearing bound or short inhomogeneous lift
needed for an irrationality proof. It also does not bound cancellation in
one aggregate weighted boundary: such a sum may have a much smaller reduced
denominator than the common multiplier for every boundary in its window.

The small-or-zero lattice construction still has its nonvanishing/independent-
pair gap. The new gcd facts alone do not close it. No small nonzero integral
forms, infinite carry violations, or complete informal solution have been
obtained, and no proof has been submitted.
