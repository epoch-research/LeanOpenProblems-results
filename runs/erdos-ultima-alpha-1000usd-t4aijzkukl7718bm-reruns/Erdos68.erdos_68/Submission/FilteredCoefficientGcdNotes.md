# Large-prime gcd bound for filtered coefficient prefixes

Verified auxiliary arithmetic, NOT a proof or disproof of Erdős 68.
`Submission/Spec.lean` remains unchanged with its original `sorry`.

`FilteredCoefficientGcd.lean` compiles without warnings. All four printed
principal axiom audits list only `propext`, `Classical.choice`, and
`Quot.sound`.

## Exact gcd definition

For an integer sequence b, define

    G_0=1,
    G_(n+1)=gcd(abs(b_(n+1)), (n+1)*G_n).

The file proves the exact finite description

    G_n=gcd(n!, gcd_(0<=k<=n) [abs(b_k)*n!/k!]).

Thus the factorial itself is included, and the gcd concerns the
INDIVIDUAL scaled coefficients. It is not gcd(n!, sum b_k*n!/k!), nor
is it a late-window gcd with the early indices omitted.

The file also proves G_n>0 and G_n divides n!.

## General valuation theorem

Fix a prime p and suppose

    b_n = 1 (mod p) whenever n>=2 and p divides n-1.

Then, for every n>0,

    v_p(G_n) <= v_p(n).

The formal statement uses `Nat.factorization` for these exponents.

Induct along the recurrence. If p divides n, the congruence makes b_(n+1)
a p-unit, so G_(n+1) is a p-unit. If p does not divide n, the inductive
bound makes G_n a p-unit, and G_(n+1) divides (n+1)*G_n. Consequently only
the current index n+1 can contribute a p-part.

## Application to the exact filtered Lambert coefficients

For `b=BinomialFilteredLambert.filtered ks`, the hypothesis is verified
whenever every filter degree k satisfies 2<=k<p. Therefore

    v_p(G_n) <= v_p(n)

for every prime p above all filter degrees. In particular, if such a p
does not divide n, it does not divide G_n.

Principal declarations:

* `coeffGcd_eq_finite`
* `coeffGcd_pos`
* `coeffGcd_dvd_factorial`
* `prime_valuation_bound`
* `filtered_prime_valuation_bound`
* `filtered_gcd_not_dvd`

## Scope and missing step

This bounds the large-prime part of a common coefficient gcd. It gives
neither an upper bound for a reduced aggregate boundary denominator nor
a controlled integer lift outside the zero-form subspace. Small-prime
factors and late windows require separate analysis. No new family of
small nonzero integral forms has been constructed.

The entire-product reorganization was also checked against its earlier
notes: the known order-two growth and integer factorial-scaled coefficients
remain compatible with a rational endpoint relation. No stronger analytic
contradiction was found. No numerical experiment was used in the new proofs,
and no settlement of Spec.lean has been submitted.
