# Large-prime gcd bounds in late filtered windows

Verified auxiliary progress, NOT a proof or disproof of Erdős 68.
`Submission/Spec.lean` is unchanged and retains its original `sorry`.

`FilteredWindowGcd.lean` compiles without warnings and has a built olean.
Both printed principal axiom audits list only `propext`, `Classical.choice`,
and `Quot.sound`.

## Exact window quantity

For an integer sequence b and H<=N, define

    G(H,N)=gcd(N!, gcd_(H<=k<=N) [abs(b_k)*N!/k!]).

This includes the factorial and the INDIVIDUAL scaled coefficients in the
late window. It neither includes earlier coefficients nor takes the gcd of
their summed boundary.

## General theorem

Let p be prime. Suppose

    b_p = 1 (mod p),
    b_n = 1 (mod p) whenever n>=2 and p divides n-1.

If H>=2 and N>=2H, then

    v_p(G(H,N)) <= v_p(N).

The formal statement uses `Nat.factorization` for the prime exponents.

### Proof

If p>N, p does not divide N!, so it does not divide G.

If p<=N-H+1, choose

    u=p*floor((N-1)/p)+1.

Then H<=u<=N, u>=2, and b_u is a p-unit by the predecessor congruence.
There is no multiple of p strictly between u and N. Consequently
v_p(N!/u!)<=v_p(N), and divisibility of G into abs(b_u)*N!/u! gives
the result.

In the remaining case N-H+1<p<=N, the assumption N>=2H gives H<=p and
N<2p. Use the prime index u=p, whose coefficient is a p-unit. The quotient
N!/p! is also a p-unit.

## Filtered Lambert application

The two coefficient congruences are verified by
`BinomialFilteredLambert` whenever every filter degree k satisfies
2<=k<p. The new theorem

    filtered_window_prime_valuation_bound

therefore applies directly to the actual normalized row-cancelling
coefficients. The result is not an inheritance assertion for the
small-tail carry.

Other declarations include `factorial_quotient_not_dvd`,
`quotient_valuation_le_last`, `bound_from_unit_index`,
`exists_pred_unit_index`, and `window_prime_valuation_bound`.

## Scope and unresolved application

H and N here are FACTORIAL COEFFICIENT INDICES. When applying this to a
raw-tail window, the sum of the operator shifts must still be included in
those indices. The condition N>=2H cannot be silently read as a condition
only on the unshifted raw-tail starting index.

The theorem controls no small-prime part of G and no representation-weight
sizes. Gcd information alone does not provide a short lift outside the
zero-form subspace. No compatible small nonzero integer-form construction
or settlement of the original conjecture was obtained. No numerical
experiment was used in the proofs, and no submission was made.
