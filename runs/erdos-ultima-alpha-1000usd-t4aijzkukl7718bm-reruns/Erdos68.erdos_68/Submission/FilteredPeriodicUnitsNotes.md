# Periodic small-prime units for filtered Lambert coefficients

Verified auxiliary arithmetic, NOT a proof or disproof of Erdős 68.
`Submission/Spec.lean` is unchanged and retains its original `sorry`.

## Periodic unit theorem

Let b_n be `BinomialFilteredLambert.filtered ks n`, where every filter
is `a_n -> a_n - choose(n,k)*a_(n-k)` with positive degree k.
For a prime p, if every degree satisfies k<p^(r+1), then

    b_(p^(r+1)*(p*t+1)) = 1 (mod p)     for every t>=0.

This is `filtered_periodic_unit` in `FilteredPeriodicUnits.lean`.

The proof has two parts:

* Iterated Lucas congruences show that p divides choose(p^s*m,k) when
  0<k<p^s. Thus all filters preserve the coefficient at that index.
* Prime-power scaling reduces the original coefficient modulo p to
  a_(p*t+1)+(p*t+1)!. At t=0 the prime-power theorem applies; at t>0,
  the predecessor congruence gives a_(p*t+1)=1 modulo p and p divides
  the factorial.

## Unrestricted prime-power endpoints

`filtered_prime_power_unrestricted` proves

    b_(p^(r+1)) = 1 (mod p)

for ANY list of positive filter degrees, without an upper bound.
Degrees above the index have zero binomial coefficient; a degree equal
to the index multiplies b_0=0; all other degrees have binomial coefficient
divisible by p. This strengthens the earlier bounded-degree endpoint
statement. It still does not assert that the coefficient is exactly one.

## Late-window valuation bound

For the existing quantity

    G(H,N)=gcd(N!, gcd_(H<=k<=N) [abs(b_k)*N!/k!]),

`filtered_window_small_prime_bound` proves, under

    H+p^(r+2)<=N,
    0<k<p^(r+1) for every filter degree,

that

    v_p(G(H,N)) <= p^(r+2) * Nat.clog p N.

`Nat.clog` is the natural ceiling logarithm. The proof picks the last
index u=p^(r+1)*(p*t+1) before N. It lies in the window and N-u<p^(r+2).
Since b_u is a p-unit, v_p(G)<=v_p(N!/u!). Finally

    N!/u! <= N^(N-u) <= p^(p^(r+2)*Nat.clog p N).

The intermediate declarations `exists_progression_index`,
`window_valuation_le_quotient`, and `factorial_quotient_le_pow` are also
verified. The indices H,N remain factorial coefficient indices, not
unshifted raw-tail sample indices.

## Verification and remaining limitation

The file compiles without warnings and has a built olean. All four printed
principal axiom audits use only `propext`, `Classical.choice`, and
`Quot.sound`. No numerical experiment is used as a premise.

For fixed filters and a fixed prime this is a logarithmic valuation bound
in sufficiently long windows. It supplies no bound on the complete Bezout
weights or on a useful integral lift outside the zero-form subspace.
In particular, the gcd being small must not be misread as an upper bound
on the reduced boundary denominator: it can instead make the corresponding
modular index large. The earlier full-weight and projection gaps remain.

No small nonzero integral-form family or complete informal solution of the
original conjecture has been obtained. No proof has been submitted.
