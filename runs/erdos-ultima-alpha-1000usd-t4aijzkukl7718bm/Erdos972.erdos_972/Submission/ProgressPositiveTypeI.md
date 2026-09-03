# Positive remainder as a nonlinear Type-I function

The original conjecture is STILL UNSOLVED. Spec.lean is unchanged with its
original sorry. No prime-pair lower bound or irrational counterexample was
obtained, and no final proof was submitted.

## New verified structural results

RemainderPositiveTypeI.lean, namespace Erdos972RemainderPositiveTypeI.
Write Lambda=A+R for the actual Vaughan split with cutoffs U,V. For U>=1
and every V (even V=0):

- `typeIIPart_isPrimePow_nonpos`: R(n)<=0 on every prime power.
- `mangoldt_le_positive_typeI`: Lambda(n)<=max(A(n),0) for every n.
- `positive_remainder_eq_negative_typeI`:

      max(R(n),0) = max(-A(n),0).

- `negative_remainder_eq_majorant_residual`:

      max(-R(n),0) = max(A(n),0)-Lambda(n).

The proof uses the nonpositivity of the Mobius function on prime powers.
A divisor of a prime power is either 1 or another prime power; the positive
Mobius cutoff removes the divisor 1 from the tail. The tail Mangoldt factor
is nonnegative. Outside prime powers, Lambda vanishes, giving the exact
positive-part identity.

Thus the positive remainder has a precise description not involving an
unresolved Mangoldt evaluation. It is not merely supported on numbers with
a small prime factor. The earlier linear positive-mass lower bound remains
valid; this identity does not make the positive mass negligible.

## Finite gcd-pattern profile

RemainderGcdProfile.lean, namespace Erdos972RemainderGcdProfile.
For D=UV, define

    affineProfile(U,V,r,x)
      = x * divisorPolynomial(D,slopeCoeff(U),r)
        + divisorPolynomial(D,constantCoeff(U,V),r),
    positiveRemainderProfile = max(-affineProfile,0).

For U>=1, V>0 and n>V:

    max(R(n),0)
      = positiveRemainderProfile(U,V,gcd(n,D!),log(n)).

Every realized pattern divides D!, so the pattern set is finite. Within
one fixed pattern, the profile is Lipschitz in its real logarithmic argument
with constant D. Consequently, if m,n>V have the same gcd with D!,

    |max(R(m),0)-max(R(n),0)| <= D*|log(m)-log(n)|.

## What is NOT proved

The positive Type-I part is now a verified genuine majorant, but no sufficient
mean or covariance estimate for that nonlinear majorant has been established.
The existing estimates for A itself cannot simply be applied to max(A,0).
Also, D! is not in the verified modulus range at the main power-growing
cutoffs. A finite pattern description does not remove that uniformity issue.

Reconsideration of rough-composite positive products still leaves the
complementary signed contribution uncontrolled. No strict centered
four-factor gap or sufficient sublinear prime correlation lower bound was
obtained. These structural results are not a settlement of Erdos 972.

Both files compile, and AuditRemainderPositiveTypeI.lean audits the seven
principal declarations using only propext, Classical.choice and Quot.sound.
Spec.lean and its sole import remain untouched.
