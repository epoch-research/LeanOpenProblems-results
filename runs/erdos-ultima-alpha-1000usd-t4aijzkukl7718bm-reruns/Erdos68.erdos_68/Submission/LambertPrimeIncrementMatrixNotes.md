# Simultaneous prime-modulus control of Lambert increments

Verified auxiliary arithmetic, NOT a proof or disproof of Erdos 68.
Submission/Spec.lean remains unchanged with its original sorry. No settlement
has been obtained or submitted.

LambertPrimeIncrementMatrix.lean compiles without warnings and has a built
olean. Its four printed principal axiom audits contain only propext,
Classical.choice, and Quot.sound. There are no proof holes or numerical
premises.

## Exact matrices

Let a_n be the original natural Lambert coefficients and let p be prime.
For m<=p and 0<=i,j<m define integer matrices

    C_ij = a_(p+i-j) * choose(p+i,j),
    R_ij = a_(p+i-j) * (p+i)!/(p+i-j)! = j!*C_ij.

The file proves, over ZMod p,

    C_ij = choose(i,j),
    R_ij = i descendingFactorial j.

Lucas' congruence gives the binomial identity. If j<=i then
p<=p+i-j<2p, so the existing first-band Lambert congruence gives
 a_(p+i-j)=1 modulo p. If j>i, the binomial factor vanishes modulo p,
so no congruence for that earlier coefficient is needed.

Consequently both matrices are lower triangular modulo p, with

    det(C)=1,
    det(R)=product_(i=0)^(m-1) i! != 0.

The last nonzero assertion uses m<=p. It is not inferred just from the
formal product expression.

## Simultaneous residue lift

For every vector v in (ZMod p)^m, simultaneous_residue_lift proves the
existence of natural weights w_j with 0<=w_j<p and

    sum_j R_ij*w_j = v_i modulo p    for every i<m.

This is genuinely simultaneous control of m residues, not just one
boundary, and the weight bound is explicit. The proof uses the verified
invertibility and takes the canonical natural representatives.

## Exact prefix connection

Write S_n=sum_(k<=n) a_k/k!. The file verifies, as a rational identity,

    R_ij=(p+i)! * (S_(p+i-j)-S_(p+i-j-1)).

Thus these are actual shifted prefix increments of the target's Lambert
regrouping, not an unrelated matrix or a comparison series.

Principal declarations:

* binomialMatrix_mod
* binomial_det_mod
* raw_det_mod
* raw_det_mod_ne_zero
* simultaneous_residue_lift
* rawMatrix_prefix_identity.

## Remaining gap

This solves a scaled system modulo ONE prime. It does not clear all
prime-power denominators of all shifted boundaries, and no useful bound
for combining such local solutions has been obtained. Unlike a single
prime increment, the shifted increments also involve composite indices;
preservation of previously imposed row-annihilation constraints is not
asserted. Nor is the same matrix asserted to be the row-subtracted or
filtered matrix in the available analytic detector.

Therefore the theorem supplies no small, nonzero integer linear-form
family. Full integrality, compatibility with row cancellation, and an
adequate global size estimate remain essential unproved requirements.

The compilation log is /tmp/lambert_prime_increment_matrix.log. The API
exploration file /tmp/PrimeMatrixAPI.lean is not part of the submission.
No numerical search was run. All compilation and axiom checks have
completed; no process is pending. No complete informal proof or disproof
of the original conjecture has been found.
