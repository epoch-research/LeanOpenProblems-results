# Verified boundary-lattice framework: still a nonvanishing gap

This is auxiliary progress, not a settlement of Erdős 68. Spec.lean remains
unchanged with its original sorry. No proof or disproof has been submitted.

The four files below compile without warnings, have built oleans, and their
printed principal axiom audits contain only propext, Classical.choice,
and Quot.sound.

## LambertBoundaryClearing.lean

For any finite shift list ds define

    P(ds)=product_(d in ds) d!,
    C(ds,H)=(H+sum(ds))! / P(ds).

The file proves P divides the indicated factorial, C is positive, and C
clears the raw boundary at EVERY n<=H. More generally, if n!*r(n) is always
integral, then C(ds,H)*rawApply_ds(r)(n) is integral for n<=H.

It then defines the rational raw operator rawApplyQ and

    boundary(ds,n)=rawApplyQ_ds(prefixQ)(n).

The real cast agrees with the previously defined rawApply. The reduced
boundary denominator divides C(ds,H), and the lcm over any finite collection
of n<=H also divides C(ds,H). These are boundary_den_dvd and boundary_lcm_dvd.

For the lattice experiment's shifts ds=[2,...,K], H=3K, this gives exactly

    C0=(M+3K)!/product_(d=2)^K d!,  M=2+...+K.

The proof uses the earlier binomial-coefficient integrality theorem for
normalized shifts and the verified identity rawApply=P*applyShifts. No
termwise denominator or external-computation assumption is required.

## BoundaryPigeonhole.lean

bounded_modular_relation proves: for positive C, if C<(Q+1)^D, any D integer
residues b_i have a relation w_i with

    w != 0, |w_i|<=Q, C divides sum_i w_i*b_i.

This is an ordinary finite pigeonhole proof in ZMod C, applied to the box
(Fin (Q+1))^D. No LLL assertion is used.

small_integral_form then proves: if C*B_i are integral and
|A*x-B_i|<=eta for integer A, there are such nonzero bounded weights with
an integral aggregate boundary b=sum_i w_i*B_i, and

    |(A*sum_i w_i)*x-b| <= D*Q*eta.

IMPORTANT: neither the coefficient pair nor the real value is asserted to
be nonzero. The theorem explicitly allows both kinds of zero.

## LambertBoundaryForms.lean

Defines the integer coefficient

    coefficient(ds)=product_(d in ds)(d!-1),

and verifies the exact affine form identity. window_small_or_zero_form
combines the clearing, pigeonhole and total analytic estimates.

Here K counts the cancelled rows: ds=[2,...,K+1]. With H>=4, D sample
indices H,...,H+D-1, and

    C(ds,H+(D-1)) < (Q+1)^D,

it supplies nonzero weights |w_i|<=Q, integral aggregate boundary b, and

    |(coefficient(ds)*sum_i w_i)*alpha-b|
      <= D*Q*2^(K+1)/(K+1)^(floor(H/2)-1).

All infinite sums and their operator interchanges were verified earlier in
LambertTailRows and LambertTotalBounds. The Stirling/asymptotic selection of
Q in the lattice notes is still informal; the finite conditional bound is
now fully verified.

## IntegerFormCriterion.lean

rational_small_form_zero proves that if x=r is rational, any integer form
with absolute value less than 1/den(r) is exactly zero.

irrational_of_independent_small_pairs proves that, for each epsilon>0,
two integer pairs (a,b),(c,d) with ad-bc!=0 and both errors less than epsilon
would imply Irrational x. This is a sufficient criterion, not a construction
of the pairs for alpha.

## Remaining mathematical problem

No uniform independent-pair theorem, nonzero small-form construction,
or infinite original carry-change theorem has been obtained. The finite
LLL evidence does not fill this gap. The new framework makes the distinction
between nonzero weights and nonzero integer forms explicit in Lean.

## Later explicit asymptotic specialization and limitation

`LambertQuadraticWindow.lean` now proves an explicit small-or-zero sequence:
H=D=K^2, Q=256*K^8, and absolute error <=256/K^2 for K>=16. This avoids
Stirling estimates. It still asserts nonzero weights only.

Moreover, `BoundedBoundaryDependence.lean` and
`quadratic_window_pair_dependence` show that for K>=32 every two cleared
forms with those particular weight bounds have dependent coefficient pairs.
Thus this specialization cannot provide the independent-pair criterion.
See LambertQuadraticWindowNotes.md for the exact determinant estimate and
scope. No nonzero-valued sequence or complete proof has been obtained.
