# Boundary-clearing lattices for shifted Lambert operators

This is mathematical analysis and an exact external finite computation,
not a Lean-verified settlement. Spec.lean is unchanged with its original
sorry. No proof or disproof has been obtained or submitted.

## Construction

Write

    Q_K(E)=product_(d=2)^K(d! E^d-1)=sum_s q_s E^s,
    M=2+...+K, A_K=Q_K(1)=product_(d=2)^K(d!-1),
    S_n=sum_(m=0)^n A_m/m!,
    B_H=sum_s q_s*S_(H+s), epsilon_H=A_K*alpha-B_H.

For the shifts H=K,...,3K let C be the lcm of the reduced denominators of
B_H, and set b_H=C*B_H in Z. Consider the full-rank lattice

    L={w in Z^(2K+1): sum_H w_H*b_H = 0 mod C}.

Each w gives integral coefficients

    a=A_K*sum_H w_H,  b=sum_H w_H*B_H,
    a*alpha-b=sum_H w_H*epsilon_H.

This clears the aggregate boundary. It is different from clearing each
individual shifted form separately, which gave large errors in the previous
test. It still does not automatically give a nonzero form or uniform bounds
on a useful basis of L.

## Completed exact test

For K=3,...,24, the script embeds L in one extra integer coordinate and
runs Sage's LLL algorithm. This is only a search procedure: the output is
checked using exact arithmetic. It verifies lattice membership and the
absolute determinant of the entire returned basis, checks every retained
boundary is integral, and reduces every nonzero coefficient pair (a,b).

Every tested K gave 2K+1 kernel rows. All 279 nonzero coefficient pairs
across the 22 tests have certified nonzero errors of absolute value below
one. The pairs span rank two in every test. Moreover, for the UNREDUCED
pairs, the gcd of the determinants of (a/A_K,b) equals one in every test.
This last statement is finite evidence, not an all-index theorem.

At K=24 there are 49 kernel rows: 47 give (a,b)=(0,0), and two give nonzero
pairs. Their reduced denominators have 845 and 847 bits, and their absolute
errors are less than 2*10^(-14). The displayed diagnostic log10 errors are
about -14.519784 and -13.802411. Their pair-reduction gcds are 13 and 7.
The maximum weight size among all 49 rows is 41 bits.

Selected results (error logs are diagnostics, not the certificates):

    K   bits C  zero pairs  projected rank  largest weight bits
    3      31       0             2                 5
    8     214       0             2                13
   12     466       0             2                19
   16     814      13             2                25
   20    1270      39             2                32
   24    1830      47             2                41

Error certification uses the exact factorial-grid interval W=2000!,

    L0=sum_(k=2)^2000 floor(W/(k!-1)),
    L0/W < alpha < (L0+2002)/W.

Artifacts:

    /tmp/lambert_boundary_lattice.py
    /tmp/lambert_boundary_lattice.log
    /tmp/lambert_boundary_lattice.json

The JSON retains every nonzero reduced pair, its original weight vector,
and its reduction gcd. If a pair was sign-normalized, its stored weights
may give the simultaneous negative of the displayed pair times that gcd.
The computation is complete, and no process remains running.

## Elementary estimates motivating the lattice (partly Lean formalized)

A common denominator is

    C0=(M+3K)! / product_(d=2)^K d!.

For an individual subset S contributing to Q_K, q_S=+/- product_(d in S)d!
and its shift is s=sum_(d in S)d. If m<=H+s, then

    m! * product_(d not in S)d! divides (M+3K)!

by multinomial integrality. Thus C0 clears every coefficient contribution
to every B_H. The finite script verifies C divides C0 as an additional check.

There is also a crude uniform analytic estimate. Put lambda_d=(d!)^(1/d).
For k<d, k!<=lambda_d^k, by monotonicity of factorial geometric means.
Also lambda_d>=sqrt(d), since (d!)^2>=d^d by pairing j with d+1-j.
For the uncancelled row d>K,

    r_d(t)=1/((d!)^floor(t/d)*(d!-1))
          <=2*lambda_d^(-t).

The sum of absolute subset weights after dividing by lambda_d^s is
product_(k=2)^K(1+k!/lambda_d^k)<=2^(K-1). Consequently, for H>2,

    |epsilon_H| <= 2^K*sum_(d>K) d^(-H/2)
                 <= 2^K*K^(1-H/2)/(H/2-1).

For K>=3 and H>=K this gives a common bound eta_K. Pigeonholing the C
fractional boundary classes with (Q+1)^(2K+1)>C gives a NONZERO WEIGHT
vector of size at most Q with integral aggregate boundary and form error
at most (2K+1)*Q*eta_K. Taking Q near C0^(1/(2K+1)), Stirling estimates
make that upper bound tend to zero: its logarithm is at most

    -(1/4)*K*log K + O(K).

This alone is NOT an irrationality proof. The weight vector can produce
(a,b)=(0,0), or under rationality can produce a different pair with zero
value. Indeed the finite tests eventually have 2K-1 zero-pair rows. The
pigeonhole bound does not control the final successive minima or guarantee
two independent projected pairs with small errors.

## Missing infinite step and prime-test limitation

A uniform theorem supplying two independent coefficient pairs with errors
tending to zero would suffice. The finite LLL results do not establish such
a theorem, and no bound for the required final successive minima is proved.

The earlier prime-last-weight nonvanishing test cannot simply be imposed
after integral boundary clearing. `PrimeLeadingForms.unit_integral_value_last_dvd`
now verifies that, at a unit coefficient index p, an integral operator value
on a rational input of denominator less than p forces p to divide its last
weight. Taking input zero applies this to an integral boundary when p>1.
Thus this very clearing condition defeats the prime nondivisibility test.
A separate nonvanishing or independent-pair argument remains necessary.

## Lean verification update

`LambertRawBounds.lean` now verifies the factorial-geometric-mean estimates,
the factorial-square lower bound, and the per-row bound for arbitrary raw
shift lists. In particular it proves both

    |rawApply_ds(r_d)(n)| <= 2^(length(ds)+1)/lambda_d^n

and the weaker denominator d^floor(n/2). It also verifies the scaling relation
to applyShifts and exact annihilation of selected rows. Its five principal
axiom audits use only the permitted axioms. See LambertRawBoundsNotes.md.
LambertTailRows.lean now verifies the exact infinite row decomposition and
interchange with raw operators. LambertTotalBounds.lean verifies the explicit
bound, in this note's indexing, for K>=2 and H>=4:

    |epsilon_H| <= 2^K / K^(floor(H/2)-1).

This uses a telescoping p-series comparison instead of an integral. The common
denominator and finite pigeonhole argument are now verified in
LambertBoundaryClearing.lean and BoundaryPigeonhole.lean. Their combination
with the total error estimate is window_small_or_zero_form in
LambertBoundaryForms.lean. The Stirling/asymptotic calculation remains informal.
The independent-pair/nonvanishing gap is unchanged. See
LambertTotalBoundsNotes.md for the exact Lean indexing.

See LambertBoundaryFrameworkNotes.md for the newest verified declarations
and the independent-pair sufficient criterion. Nonvanishing remains unproved.

## Later determinant constraint (not a solution)

BoundedBoundaryDependence.lean proves that two integral aggregate boundaries
from D common-coefficient rows with row error <=eta and weights <=Q have
zero projected determinant whenever 2*(D*Q)^2*eta<1. The common retained
coefficient A cancels out. Independence therefore requires a larger weight
budget than this threshold. This does not refute the finite linear-window
LLL tests above and does not bound their final minima from above.

For the distinct quadratic window H=D=K^2 and Q=256*K^8,
LambertQuadraticWindow.lean proves both arbitrarily small-or-zero forms and,
for K>=32, dependence of every two such cleared coefficient pairs. See
LambertQuadraticWindowNotes.md. No nonvanishing theorem for those forms or
settlement of Spec.lean follows.

## Later last-coefficient and criterion audit

A later review reconsidered whether a final coefficient, chosen nonzero
modulo a prime or prime power, could replace the missing nonvanishing theorem.
No compatible bounded vector was constructed. Clearing an aggregate boundary
still forces the last-weight divisibility in PrimeLeadingForms, and neither
pigeonholing nor the existing bounds select a vector outside the zero-form
subspace. No quantitative claim about the final useful successive minima
was proved.

The existing irrationality criteria were also cross-checked against the
unconditional representations. The small rowwise tails still lack the
required congruences. The congruence-preserving representation still permits
quadratic tails at prime indices, which occur inside the local intervals.
The averaged prime-deficit and twice-prime criteria still have unproved
infinite-occurrence hypotheses. No combination yielding an unconditional
proof was found, and no new Lean declaration was added in this review.
Spec.lean remains unchanged with its original sorry; nothing was submitted.
