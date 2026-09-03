# Prime-power local control for normalized increment matrices

Verified auxiliary arithmetic, NOT a proof or disproof of Erdos 68.
Submission/Spec.lean remains unchanged with its original sorry. No settlement
has been obtained or submitted.

PrimePowerIncrementMatrix.lean compiles without warnings and has a built
olean. All seven printed principal axiom audits contain only propext,
Classical.choice, and Quot.sound. There are no proof holes or numerical
premises.

## General normalized matrix

For an integer sequence c and a center N define

    C_ij = choose(N+i,j)*c_(N+i-j),  0<=i,j<m.

Suppose p is prime, N=p^r*t, m<=p^r, and c_N=1 modulo p.
The file proves

    det(C)=1 modulo p.

The new choose_translate lemma gives

    choose(p^r*t+i,j)=choose(i,j) modulo p  (i,j<p^r).

Thus all entries above the diagonal vanish modulo p, and every diagonal
entry is c_N=1. No assumption on the coefficients below the diagonal is
needed; in particular no unproved prime-power-band congruence is used.

## Every power of the local prime

Since det(C) is coprime to p, it is coprime to p^e for every e. The theorem
prime_power_residue_lift proves that for every vector v modulo p^e there
are natural w_j<p^e satisfying

    sum_j C_ij*w_j=v_i modulo p^e    for every i<m.

This is simultaneous local control, with an explicit bound on the chosen
representatives. It does not silently replace p^e by p in that bound.

## Actual original and filtered coefficients

The existing periodic-unit theorems apply at

    N=p^(r+1)*(p*t+1).

They give c_N=1 modulo p for the original Lambert coefficients. They also
give it for the exact binomial-filtered coefficients, provided each
filter degree k satisfies 0<k<p^(r+1).

The new theorems lambert_prime_power_lift and filtered_prime_power_lift
apply the general matrix result with m<=p^(r+1). Thus the local result
extends beyond the initial prime band and includes these actual filtered
coefficients. It is not a comparison-sequence assertion.

## Essential normalization

For S_n=sum_(k<=n)c_k/k!, normalized_prefix_identity proves exactly

    C_ij = (N+i)!/j! * (S_(N+i-j)-S_(N+i-j-1)).

The input column normalization 1/j! matters. The bounded residues w_j are
not automatically bounded INTEGRAL weights w_j/j! for ordinary prefix
increments. Clearing those factors introduces an additional cost. The
factorial and index-shift factors in connecting filtered coefficients to
the earlier raw operators likewise have not been discarded.

## Verified failure of arbitrary residue control without normalization

The later declarations unnormalized_det_zero and
unnormalized_not_surjective make the normalization issue explicit. For
ANY integer coefficient sequence c and center N, set

    R_ij=j!*C_ij.

The file verifies that these are the ordinary row-factorial-scaled prefix
increments, without division of the input weights by j!. If p<m, column
j=p vanishes modulo p, because p divides p!. Consequently det(R)=0
modulo p and R is not surjective on (ZMod p)^m.

This does not rule out a particular required residue vector or a different
larger input system. It does rule out simply transferring the normalized
arbitrary-residue theorem to ordinary integral weights at these small
primes. No global impossibility claim is inferred.

## Remaining global gap

Invertibility modulo every power of ONE prime does not give a controlled
simultaneous lift for all prime-power denominators. The useful centers
and block sizes depend on p, and compatibility between different local
corrections has not been established with a sufficient global height bound.
No full-target nonzero integer-form family with errors tending to zero
has been constructed.

Principal declarations:

* choose_translate
* determinant_one_mod
* prime_power_residue_lift
* normalized_prefix_identity
* lambert_prime_power_lift
* filtered_prime_power_lift.

No numerical search was run. The compilation log is
/tmp/prime_power_increment_matrix.log. The exploratory API file
/tmp/PowerMatrixAPI.lean is not part of the submission. All compilation
and axiom checks have completed; no process is pending. No complete
informal solution to the original conjecture is awaiting formalization.
