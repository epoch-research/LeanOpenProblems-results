# Special compatibility of the actual tail target

Verified auxiliary arithmetic, NOT a proof or disproof of Erdos 68.
Submission/Spec.lean remains unchanged with its original sorry. No settlement
has been obtained or submitted.

IncrementTargetCompatibility.lean compiles without warnings and has a built
olean. Its three printed principal axiom audits contain only propext,
Classical.choice, and Quot.sound. There are no proof holes or numerical
premises.

## A target-specific fact, despite failure of general surjectivity

For any integer coefficient sequence c write

    S_n=sum_(k<=n)c_k/k!,
    R_ij=(N+i)!*(S_(N+i-j)-S_(N+i-j-1)),  0<=i,j<m, m<=N.

These are the unnormalized integer increment matrices from the preceding
file. The new file proves exactly, for every rational endpoint x,

    (N+i)!*(x-S_(N+i)) + sum_j R_ij
      = (N+i)!*(x-S_(N+i-m)).

If den(x)<=N+i-m, the right side is an integer multiple of

    (N+i) descendingFactorial m = (N+i)!/(N+i-m)!.

Thus the unit vector of input weights solves the particular tail-target
congruence for every modulus dividing this factorial quotient. Failure of
surjectivity for arbitrary residue vectors does NOT exclude this target.
The theorem target_factorial_quotient retains the rational endpoint's
explicit denominator condition.

## Why this does not supply smaller errors

The same exact identity identifies the correction as a BACKWARD shift of
the prefix. For nonnegative c the sum of increments is nonnegative, so

    (N+i)!*(x-S_(N+i)) <= (N+i)!*(x-S_(N+i-m)).

This is corrected_tail_not_smaller. It applies to the original nonnegative
Lambert coefficients. For the signed filtered coefficients the identity
and divisibility are still valid, but this monotonicity is not asserted.

The correction is therefore not an independent small-form construction.
A scheme combining local congruences must still account for these shifted
errors; compatibility alone does not make the resulting integer form both
nonzero and small. No such global scheme was obtained here.

Principal declarations:

* reverse_telescope
* unit_block_identity
* corrected_tail_eq_earlier
* target_factorial_quotient
* unit_block_nonneg
* corrected_tail_not_smaller.

The earlier common-center review also found no compatible complete clearing
and height estimate. Conditions used to guarantee local triangularity are
sufficient conditions, not necessary conditions for matrix invertibility;
no global impossibility claim is inferred from their incompatibility.

No numerical search was run. The compilation log is
/tmp/increment_target_compatibility.log. All compilation and axiom checks
have completed; no process is pending. No complete informal proof or disproof
of the conjecture is waiting to be formalized.
