# Recurrence-based strict upper approximations (not a solution)

Write alpha for the Erdős 68 series, d_N=N!-1, and

    S_N = sum_(k=2)^N 1/d_k,
    U_N = S_N + 1/(N*N!).

`Submission/CorrectedApprox.lean` uses N=n+3 to prove:

* U_N is rational and strictly decreasing for N>=3;
* U_N tends to alpha;
* 0 < U_N-alpha < 1/(N*(N+1)*N!).

The exact difference is

    U_N-U_(N+1)
      = (d_(N+1)-N*(N+1)) / (N*(N+1)^2*N!*d_(N+1)).

Its numerator is positive for N>=3. The error upper bound follows by
comparing alpha with S_(N+1), and using

    1/d_(N+1) > 1/((N+1)*N!).

Thus this approximation family does not have the nonvanishing gap of
rounded factorial-grid approximations: its error is strictly positive at
every index in its stated range.

## The termwise denominator-clearing obstruction

The same Lean file proves that for N>=5 and any positive integer M such that

    d_N | M,   N*N! | M,

one has

    M*(U_N-alpha) > 1.

Indeed d_N is coprime to N*N!, so M >= d_N*N*N!. Also
U_N-alpha > U_N-U_(N+1). Multiplying the displayed exact difference by this
lower bound for M already gives a number greater than 1. The proof uses the
simple factorial estimate N! >= 4*N*(N+1) for N>=5.

This rules out the elementary approach that clears every denominator in
U_N term by term and tries to obtain a positive integer less than 1.
It does NOT prove any analogous lower bound for the reduced denominator of
U_N; a reduced denominator could involve cancellation between its summands.
No useful bound exploiting such cancellation has been obtained.

All three printed axiom checks in CorrectedApprox.lean list only propext,
Classical.choice, and Quot.sound. This file does not settle the original
conjecture. Submission/Spec.lean remains unchanged.

## A verified reduced-denominator cancellation

`Submission/CorrectedDenominatorCancellation.lean` gives an exact counterexample
to the proposed auxiliary claim that the last included denominator d_N must
divide the reduced denominator of S_N or U_N. This is NOT a disproof of the
irrationality conjecture.

At N=137, the prime 139 divides d_137=137!-1, but it divides neither the reduced
denominator of S_137 nor that of U_137. The Lean theorem names include:

* `factors_139_through_137`: among k=2,...,137, precisely k=69,122,137 have
  139 | k!-1;
* `quotient_residues_139`: the corresponding (k!-1)/139 residues are
  6,49,73 modulo 139;
* `partial_sum_137_den_coprime_139`;
* `correctedApprox_134_den_coprime_139` (the indexing is N=n+3);
* `canceled_prime_in_correctedApprox`;
* `last_denominator_need_not_survive_correction`.

The inverse residues are 116,122,40, which sum to 278=2*139. Thus the three
139-denominator contributions cancel. All other terms, including the
correction 1/(137*137!), have denominators coprime to 139.

The file uses ordinary `decide`, `norm_num`, and arithmetic proofs, not
`native_decide`. Its final axiom check lists only the permitted axioms.
This example does not exclude weaker lower bounds on reduced denominators,
and gives no positive result toward an irrationality proof. Spec.lean remains
unchanged.
