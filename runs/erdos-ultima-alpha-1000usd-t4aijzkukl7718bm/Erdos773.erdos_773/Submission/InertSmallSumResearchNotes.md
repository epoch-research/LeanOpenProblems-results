# Base-three small-total-digit-sum obstruction

This is NOT a disproof of Erdős 773. The original conjecture in `Spec.lean`
remains admitted for 0 < epsilon <= 1/3.

## Exact construction

For B=864*(t+6), put x=135*(t+6)=5*B/32 and y=297*(t+6)=11*B/32.
The four words, constant coefficient first, are

    [21,0,219,0,480,0,219,0,309,0,1056,x,0,y,0,0,1]
    [309,0,219,0,1056,0,219,0,21,0,480,y,0,x,0,0,1]
    [219,0,21,0,480,0,309,0,219,0,1056,y,0,x,0,0,1]
    [219,0,309,0,1056,0,21,0,219,0,480,x,0,y,0,0,1]

They have identical complete digit histograms, leading digit 1, all lower
digits divisible by 3, and constants congruent to 3 modulo 9. Their common
digit sum is 2305+B/2 < B, and every digit is less than B/2.
The common squared-digit sum is 1537381+106434*(t+6)^2.
The evaluated roots satisfy v0^2+v1^2=v2^2+v3^2 nontrivially.

At t=0, B=5184. The digit sum is 4897, the squared-digit sum is 5369005,
and the root gcd is exactly 3. An unbounded primitive subfamily is given by

    t=55332*u+55326, B=47806848*(u+1).

The Bezout identity used to prove the gcd statement is

    (43333*B^2 + 985120*B^4)*v0 + 226836*v3
      = 47806848 + 16073*v0 + (4092+184656*B^2)*v1
        + (1225+43387*B^2+985120*B^4)*v2.

Thus the gcd divides 47806848. For that subfamily v0=21 modulo 47806848,
and gcd(47806848,21)=3; all four roots are divisible by 3.

## Algebraic source: rational coefficients and empty positions

Let

    Q(X)=X^2+(1/4-3i/32)*X+(1/4+3i/32),
    R(X)=X^6+(768-288i)*X^3+(768+288i).

The real and imaginary parts of (1+i)*Q*R and (1+i)*conj(Q)*R have equal
sums of squares. Substitute X^2 for X, making all occupied exponents even.
The small fractional coefficients 5/32 and 11/32 at positions 12 and 14
can be rewritten, at X=B, as integer digits 5*B/32 and 11*B/32 at the
previously empty positions 11 and 13. This preserves the complete histogram.

There is NO contradiction with Gaussian Eisenstein irreducibility at 3.
For a fixed t the displayed digit polynomials are Eisenstein, but their norm
identity holds only after evaluation at the corresponding base B. The
underlying formal norm identity has rational, not Eisenstein, coefficients.

## Verification status

`InertSmallSumObstacle.lean` proves the identities with `ring` and the finite
histogram equality by comparing counts. The collision, non-Sidon statement,
histogram, concrete gcd, and primitive-family gcd have clean axiom audits.
The entire file now compiles with `lake env lean -s 65536`. All five printed
audits (conditions, histogram_perm, not_sidon, primitive_example, and
primitive_family) use exactly propext, Classical.choice, and Quot.sound.
The kernel recursion issue was isolated to the digit-norm computation and
resolved by `norm_num [mul_pow]` followed by `omega`, rather than expanding
the whole expression with `ring`. The final log is /tmp/inert-small-sum.log.

This replaces the previously unresolved base-three small-total-digit-sum
candidate with an explicit obstruction. It does NOT establish that every large
histogram class is bad or rule out all refinements of digit constructions.
