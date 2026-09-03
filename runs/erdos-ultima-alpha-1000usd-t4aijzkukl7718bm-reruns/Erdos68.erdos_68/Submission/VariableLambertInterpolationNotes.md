# Short-window variable Lambert interpolation

External exact construction test, NOT a Lean theorem and NOT a settlement
of Erdős 68. Spec.lean is unchanged and retains its original sorry. No
complete informal proof or disproof has been obtained.

## Construction

Let S_n=sum_(m=0)^n a_m/m! be the Lambert prefix, and let

    r_d(n)=1/[(d!)^floor(n/d)*(d!-1)].

Instead of the constant shift operator of degree M=2+...+K, this test seeks
rational weights on K selected indices n_i starting at H, satisfying

    sum_i w_i=1,
    sum_i w_i*r_d(n_i)=0,   2<=d<=K.

Start with the candidate indices H,...,H+M. Rescale each row independently
to obtain the integer matrix with constant row one and rows

    (d!)^(floor((H+M)/d)-floor((H+i)/d)).

Take its first K pivot columns, and solve the resulting square rational
system with right side (1,0,...,0). Each tested matrix had full row rank.
The selected indices need not be consecutive, and the reported window
length D is last_index-H+1, not the number K of nonzero slots.

The boundary B=sum_i w_i*S_(n_i) is reduced to a/b, b>0. The actual tested
form is b*alpha-a. This clears only the reduced aggregate boundary. It does
not multiply by every auxiliary weight denominator unnecessarily.

For comparison, clearing the weights themselves gives integers v_i. Their
sum is divisible by every d!-1, 2<=d<=K, as required by the previously
verified variable-row divisibility theorem. This equality is checked too,
but it is not substituted for the reduced boundary denominator.

## Parameters and results

K=2,...,20, with the distinct starting indices

    H in {K, 2K, 3K, max(K,floor(K^2/4)),
          max(K,floor(K^2/2)), K^2, 2K^2}.

All 123 cases completed. Every exact full-target error interval is outside
[-1,1]: 99 negative-large cases and 24 positive-large cases. There are no
small or ambiguous cases.

The windows are appreciably shorter than the original constant operator.
For example, at K=20,H=400, D=26 (versus raw operator degree 209), but the
reduced boundary denominator has 3,542 bits and the diagnostic base-two
logarithm of the absolute integer-form error is approximately 2,171.
These diagnostics are not certificate premises.

This finite failure is not an asymptotic impossibility theorem and excludes
no other index selection, free-parameter optimization, or variable operator.
It supplies no infinite family of useful integer forms.

## Exact enclosure and independent audit

The construction accumulates the divisor coefficients a_m/m! to obtain S_n.
The independent audit instead reconstructs every sampled prefix from finite
geometric rows:

    S_n=sum_(d=2)^n [(d!)^floor(n/d)-1]
                       / [(d!-1)*(d!)^floor(n/d)].

It verifies nonsingularity of each selected matrix, the normalization and
every row cancellation, the common weight denominator and its integer
weights, the reduced aggregate boundary, and every stored error interval.
Nonsingularity is checked by independent rational elimination; it is not
inferred from the construction's pivot report.

Error intervals use the exact factorial grid N=2500:

    W=N!, L=sum_(n=2)^N floor(W/(n!-1)),
    L/W < alpha < (L+N+2)/W.

The audit reconstructs these intervals and rechecks every classification
using a second grid at N=2517. All 123 audits passed.

Artifacts:

* /tmp/variable_lambert_interpolation.py, .json, .log
* /tmp/variable_lambert_interpolation_audit.py, .log

Neither computation is a Lean theorem or a premise of the final conjecture.
Both computations have completed; nothing is pending.

## Boundary-lattice review

The prime last-coefficient test still cannot simply be imposed on an
integrally cleared vector: the existing PrimeLeadingForms theorem forces
last-weight divisibility. Restricting supports to prime final indices also
reduces the available sampling dimension; no compatible pigeonhole and
height bound was obtained. Nor was a uniform bound on the useful projected
minima or their integral lifts established.

The exact common boundary denominator in the existing six linear-window
geometry examples is already equal, or within a tiny factor, to the known
factorial-quotient clearing denominator. No useful uniform denominator saving
was found in this review. That is a finite observation, not an assertion of
all-index equality or a lower bound for every alternative construction.

No new Lean proof of the original conjecture was produced, and no new
submission check was made. Spec.lean remains unresolved.
