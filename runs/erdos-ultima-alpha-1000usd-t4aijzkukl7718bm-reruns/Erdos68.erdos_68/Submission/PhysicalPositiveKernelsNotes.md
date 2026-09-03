# Positive quadratic kernels on the physical index domain

This is new verified auxiliary progress, NOT a settlement of Erdős 68.
Spec.lean is unchanged and still contains its original sorry. No proof or
disproof has been submitted.

## Main difference from the previous positive kernels

The older ansatz was

    P(n,t)=A*t^J+(1-t)*S(n,t), S>=0 at factorial nodes.

Its omitted-column lower bound is correct for that ansatz, but need not hold
for a kernel certified positive by a different construction.

Write the original row index as x>=2. The new quadratic ansatz is

    P(x,t)=a^2+2a(1-t)R(x)+(1-t)^2 S(x)
          =[a+(1-t)R(x)]^2+(1-t)^2 [S(x)-R(x)^2].

If S(x)>=R(x)^2 only for x>=2, then P is nonnegative at every physical row,
for every real t. It need not be nonnegative at the auxiliary endpoints
x=0 and x=1. This relaxation is essential in the construction.

For rational polynomials H_1,H_2, impose the column identities

    x H_1(x-1)-H_1(x) = -2a R(x)-S(x),
    x^2 H_2(x-1)-H_2(x) = S(x).

Then P is a valid rational telescoping kernel with J=2, and

    B=H_1(1)+H_2(1)=2a[R(0)+R(1)],
    sum_(x>=2) P(x,1/x!)/(x!-1)=a^2*alpha-B.

There is no forced A/2^J baseline in this identity.

## General Lean verification

PhysicalPositiveKernels.lean proves:

* quadratic_kernel_identity;
* quadratic_kernel_nonneg;
* quadratic_boundary;
* hasSum_quadratic_error, the exact convergent squared-error decomposition.

The positivity hypothesis is only at the physical natural row indices. The
variance may vanish. The later `KernelNonvanishing.lean` now gives automatic
strict positivity when A!=0, so a separately specified positive row is no
longer needed. This does not supply small integral forms.

## Exact finite certificate

PhysicalPositiveKernelExample.lean verifies a rational example with

    A=4, B=5, J=2,
    deg H_1=10, deg H_2=9.

It proves an exact rational sum-of-squares identity

    P(x,t)=4*(v(x,t)^T G v(x,t)+(x-2)*w(x,t)^T H w(x,t)),

where G is 7 by 7 and H is 6 by 6. The vectors use the first six Charlier
polynomials:

    v=(1,(1-t)p_0(x),...,(1-t)p_5(x)),
    w=((1-t)p_0(x),...,(1-t)p_5(x)).

The Lean certificate uses the exact positive rational LDL decompositions,
written explicitly as positive weighted squares. The matrix solver is NOT
trusted: Lean checks the resulting polynomial identity and positivity.

The file proves:

* boundary family 2 = 5;
* kernel 4 family 2 n t >= 0 for every natural n and every real t;
* the first factorial-node row is strictly positive and less than one;
* the infinite sum is exactly 4*alpha-5;
* 0 < 4*alpha-5 < 1;
* no nonnegative residual R can express this kernel at all factorial nodes
  as 4*t^2+(1-t)*R.

The last assertion follows already at x=2, where that older ansatz would
force a row value at least one. Thus this is a genuine verified escape from
the old positive-column baseline, not a contradiction to its theorem.

Both files compile without warnings and have built oleans. Their printed
principal axiom audits contain only propext, Classical.choice and Quot.sound.

## Exact certificate artifacts and numerical discovery

The exact rational matrices and polynomials are stored in

    /tmp/physical_gram_exact_D5.json.

The reconstruction script /tmp/physical_gram_exact.py checks all five affine
constraints exactly, checks positive leading principal minors in each block,
and checks the positive rational LDL decompositions. It starts by rounding
entries to denominator 10^7 and then repairs five entries exactly; the largest
repaired matrix-entry denominator is 8400000000. It also checks both column
remainders are zero and the normalized boundary is exactly 5/4.

The finite SDP search, before exact reconstruction, used

    /tmp/physical_gram_kernel_sdp.py
    /tmp/physical_gram_feasible.py
    /tmp/write_physical_lean.py.

Here D is the polynomial degree in x, and J=2*(L+1) is the degree in t.
For general L, v contains (1-t)*p_a(x)*t^b with b<=L; the H block is weighted
by x-2. All column-image constraints are computed by exact polynomial
reduction before the numerical optimization. The displayed objectives below
are ONLY DIAGNOSTICS, not certified optimal values or exact feasible points:

    D J   diagnostic boundary B, normalized A=1
    2 2   1.10710817296894
    4 2   1.24652812532960
    5 2   1.25239181816880
    6 2   1.25334170104849
    8 2   1.25349612427052
    2 4   1.22424507366422
    3 4   1.25344034720808
    4 4   1.25349818562582

Several runs are not fully converged. No asymptotic rate or convergence to
alpha is claimed. The separate D=5,J=2 feasibility run fixes B=5/4 and gives
the exact certificate described above. No numerical matrix is imported into
Lean as an unchecked premise. All runs have completed; no process is pending.

## Remaining gap

The example supplies ONE nonzero small form, with the fixed value 4*alpha-5.
It does not make that value tend to zero. No growing family with controlled
integral A_N,B_N and errors tending to zero has been obtained. In particular,
the exploratory SDP values do not control the reduced boundary denominators.

Unlike the boundary-lattice route, positivity can ensure nonvanishing here.
The unsolved problem for this route is a simultaneous asymptotic construction
and arithmetic-height bound. This is not a complete informal proof awaiting
formalization.

## Later nonvanishing result

`KernelNonvanishing.lean` proves that every fixed nontrivial rational
polynomial kernel is eventually nonzero at factorial nodes. Combined with
nodewise nonnegativity this gives a strictly positive total form automatically.
See `KernelNonvanishingNotes.md`. The asymptotic construction and arithmetic
height gap above remains unchanged.

## Further review of the arithmetic target

A later review did not construct a growing family. Only the retained
coefficient A and aggregate boundary B must be integral. The denominators
of Gram entries or auxiliary polynomial coefficients are not additional
multipliers that must automatically be cleared. Thus their size alone
cannot be used as an impossibility argument for this approach.

Conversely, the displayed finite normalized SDP objectives approaching
alpha do not establish integer A_N,B_N with positive errors tending to
zero. Rounding a close real boundary to an integer boundary can leave an
error of order one after scaling. No proof controlling that rounding or
constructing a suitable sequence of integral boundaries was obtained.
There was no new solver run or certificate in this review, and the original
Spec.lean remains unchanged.
