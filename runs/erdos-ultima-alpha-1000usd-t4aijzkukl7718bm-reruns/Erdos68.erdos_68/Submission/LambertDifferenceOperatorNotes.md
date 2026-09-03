# Lambert row-annihilating difference operators (verified auxiliary work)

This does not settle Erdős 68. `Submission/Spec.lean` is unchanged and retains
its original sorry. No complete proof or disproof has been submitted.

`LambertDifferenceOperators.lean` and `LambertDifferenceCheck.lean` compile
without warnings. Their printed axiom audits list only `propext`,
`Classical.choice`, and `Quot.sound`.

## Exact operators

Define

    E_d r(n) = r(n+d) - r(n)/d!.

The operators commute. For the geometric row tail

    r_d(n) = 1 / ((d!)^floor(n/d) * (d!-1)),

one has E_d r_d=0 when d>0. Any finite composition containing E_d therefore
annihilates that row. These are `rowShift_commute`,
`rowShift_geometricRowTail`, and `applyShifts_geometricRowTail`.

The integral scaling is exact:

    (n+a+d)! E_d r(n)
      = (n+d+a)! r(n+d) - binomial(n+a+d,d) (n+a)! r(n).

Consequently, if (n+a)! r(n) is an integer eventually, applying the operators
with shifts ds leaves an integer after multiplication by (n+a+sum(ds))!.
This is `applyShifts_integral`.

The offset is important: after applying a shift d, the next binomial
coefficient uses the new offset a+d. Simply composing a fixed-offset
integer operator would give the wrong normalization.

Killing rows 2,...,K costs total shift 2+...+K, of quadratic order in K.
The identities do not establish a small or nonzero resulting integer.

## Exact two-row arithmetic check

Let A_m be the previously verified Lambert coefficients, and put

    S_j = sum_(m=0)^j A_m/m!,
    r_x(j) = x-S_j.

The finite values S_0=0, S_2=1/2, S_3=2/3, and S_5=29/30 give

    12 E_3 E_2 r_x(0) = 5x-33/5,
    60 E_3 E_2 r_x(0) = 25x-33.

These are `first_two_shifts` and `first_two_cleared_shifts`.
For x=alpha, the existing upper bound alpha<63/50 proves

    1 < abs(25 alpha-33),

as verified by `first_two_cleared_error_large`. The raw error cannot be
treated as an integer form without clearing the rational constant.

## Exploratory finite family (not Lean-verified)

A Python exact-rational calculation tested the polynomial operator

    Q_K(E) = product_(d=2)^K (d! E^d-1).

Writing Q_K(z)=sum q_j z^j gives

    I_K = A_K alpha-B_K,
    A_K = product_(d=2)^K (d!-1),
    B_K = sum q_j S_j in Q.

For K=2,...,16 the calculation found no cancellation between A_K and the
reduced numerator of B_K. Already at K=3, B_K=33/5. At K=4 its denominator
is 315; at K=5 it is 1261260. In this finite range the reduced scaled errors
exceed one for every K>=3 and increase rapidly. The raw unscaled errors
are much smaller, but this does not remove the denominator cost.

The displayed errors used a long exact rational partial sum in place of
alpha; the coefficient and denominator calculations themselves were exact.
These are exploratory checks, not a theorem for all K and not an exclusion
of modified operator constructions.

## Analytic direction investigated

The exact Lambert function has more restrictive growth away from its poles
than the earlier rational comparison functions obtained by adding entire
functions. No theorem connecting that additional growth to irrationality
of its value at one was established. Dividing by z-1 under a hypothetical
rational value still gives integral factorial-scaled coefficients; growth
or pole locations alone do not supply the missing nonvanishing and
smallness estimates.

The main unresolved goal remains infinitely many changes of the
factorial-grid approximants in Development.lean, or another construction
of nonzero integer forms tending to zero under rationality.

## Further exact test through K=40

A later completed calculation extended the same raw family

    Q_K(E)=product_(d=2)^K(d! E^d-1),
    Q_K(E)r_alpha(0)=A_K alpha-B_K,
    A_K=product_(d=2)^K(d!-1), B_K in Q.

Artifacts:

    /tmp/lambert_operator_raw.py
    /tmp/lambert_operator_raw.log

For every tested K=2,...,40, exact rational intervals certify that the raw
error is positive at even K and negative at odd K. Its magnitude at K=40
is about 0.025544; the observed values are consistent with order 1/K.
This is finite evidence only: neither the sign nor the asymptotic has been
proved for arbitrary K.

Write B_K=b_K/c_K in lowest terms. After clearing and fully reducing the
integer coefficients, the error is

    [c_K/gcd(A_K,b_K)] * (A_K alpha-B_K).

The exact intervals certify absolute error greater than one for ALL tested
K=3,...,40. The case K=2 is the already known form alpha-1.
The common gcd equals 1 in these tests except at K=33, where it equals 1753.
Thus the earlier finite absence of cancellation through K=16 cannot be
promoted to an all-index coprimality claim. At K=40, c_K has 4006 binary digits.

The final calculation used the exact factorial-grid enclosure with
M=819, W=820!, and

    L=sum_(k=2)^820 floor(W/(k!-1)),
    L/W < alpha < (L+M+3)/W.

The upper bound follows from the number of fractional remainders and the
positive original tail beyond 820. All error classifications used rational
arithmetic; displayed decimals and logarithms are diagnostics only. An
initial run used an insufficient precision for the larger multipliers and
was replaced; its ambiguous intervals are not used in these conclusions.
A subsequent unnecessarily large-denominator computation was stopped and
replaced by the factorial-grid enclosure. The final run completed and no
computation remains pending.

This test has not been formalized in Lean. It does not settle Erdős 68 or
exclude other operators or combinations. Spec.lean is unchanged.

## Shifted starting-index test

A further completed exact calculation used

    Q_K(E)r_alpha(H)=A_K*alpha-B_(K,H),
    B_(K,H)=sum_j q_j*S_(H+j),

with the same Q_K and A_K as above. It tested K=2,...,24 and the distinct
values of H in {0,1,floor(K/2),K,2K,4K,K^2}, for 157 pairs in total.
Each rational B=b/c was reduced, and then (c*A,b) was fully reduced by
its gcd. No gcd cancellation between A and b occurred in these tests.

Only (K,H)=(2,0),(2,1) had absolute reduced integer-form error between zero
and one. All other 155 tested forms had absolute error greater than one.
There were no ambiguous intervals. Examples (logs are diagnostics):

    K   H   bits of c   log10 absolute reduced integer-form error
    8   0       81             23.421209
    8   8      122             30.917128
    8  64      466             99.503232
   16   0      466            138.966275
   16 256     2504            533.022034
   24   0     1219            365.448841
   24 576     6488           1370.888463

The error intervals used W=2000! and

    L=sum_(k=2)^2000 floor(W/(k!-1)),
    L/W < alpha < (L+2002)/W.

The script checks sum_j q_j=A_K exactly and uses gmpy2 rational arithmetic
throughout the classifications. This is external exact computation, not a
Lean verification of the finite test or an asymptotic impossibility theorem.

Artifacts:

    /tmp/shifted_lambert_operator.py
    /tmp/shifted_lambert_operator.log
    /tmp/shifted_lambert_operator.json

The computation completed; nothing is running. The separate verified result
in PrimeLeadingForms.lean supplies a rational-input nonvanishing condition
when a shifted last index is prime, but no compatible small-error family.
Spec.lean remains unchanged and no proof or disproof has been submitted.
