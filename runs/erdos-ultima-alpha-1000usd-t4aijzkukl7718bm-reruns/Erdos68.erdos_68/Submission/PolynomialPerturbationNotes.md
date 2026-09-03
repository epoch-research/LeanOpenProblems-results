# Rational reciprocal sums with polynomial additive factorial perturbations

These are mathematical notes, not Lean-verified declarations. They are NOT
a counterexample to the conjecture about the exact denominators n!-1.

The following interval construction limits approaches based only on very
close factorial growth or on denominator ratios close to integers.

## A general interval-selection observation

For each n>=N let the allowed integer denominators be every integer in
[a_n,b_n], with 0<a_n<=b_n. Suppose the two endpoint series converge, and set

    L_n = sum_(k>=n) 1/b_k,
    U_n = sum_(k>=n) 1/a_k.

If, for every n>=N,

    U_(n+1)-L_(n+1) >= 1/(a_n*(a_n+1)),

then every x in [L_N,U_N] is representable as sum_(n>=N) 1/d_n with
integer d_n in [a_n,b_n]. Indeed the finitely many intervals

    [1/d+L_(n+1), 1/d+U_(n+1)]   (a_n<=d<=b_n)

overlap consecutively: the largest adjacent displacement is
1/a_n-1/(a_n+1). Their union is exactly [L_n,U_n]. Recursively choose
a denominator leaving the residual in the next interval. Both endpoints
of the residual interval tend to zero, so telescoping proves the series
identity. In particular, if L_N<U_N, rational values occur by density of Q.

## Denominators between n! and n!+2*n^2

Take N=4, a_n=n!, b_n=n!+2*n^2. Write m=n! and x=n+1. The first term of
the tail-width series gives

    U_(n+1)-L_(n+1) >= 2/(m*(m+2*x)).

This is at least 1/(m*(m+1)) because m>=2*n for n>=4. Thus the interval
observation applies, giving rational reciprocal sums with

    n! <= d_n <= n!+2*n^2.

After adding finitely many initial reciprocal factorials, the full sum
starting at n=2 is still rational. Writing d_n=n!+epsilon_n gives

    d_(n+1)/d_n - (n+1)
      = (epsilon_(n+1)-(n+1)*epsilon_n)/d_n
      = O(n^3/n!).

The perturbations are additive polynomials, not merely a polynomial factor
multiplying n!. Thus even extremely close factorial growth does not suffice.

## Ratios approaching the integers strictly from above

A variant also fixes the sign of the ratio error. For n>=7 set

    a_n=n!-3*n^2,
    b_n=n!-n^2.

Here n!>=12*n^2 (the base case and induction suffice), so a_n>=3*n!/4>0.
The endpoint series converge by comparison with sum 1/n!. With m=n! and
x=n+1, the first term of the tail width is

    1/a_(n+1)-1/b_(n+1)
      = 2/((m-3*x)*(m-x))
      > 2/m^2.

On the other hand,

    1/(a_n*(a_n+1)) <= 16/(9*m^2) < 2/m^2.

The same selection argument therefore supplies a rational reciprocal sum
with d_n=n!-c_n, n^2<=c_n<=3*n^2, for every n>=7.

For any such choices, not only the ones supplied by selection,

    d_(n+1)/d_n-(n+1)
      = ((n+1)*c_n-c_(n+1))/d_n.

Its numerator is at least
(n+1)*(n^2-3*(n+1))>0, and it is less than 3*(n+1)*n^2. Consequently

    0 < d_(n+1)/d_n-(n+1) < 4*(n+1)*n^2/n! < 1

for n>=7. The last inequality follows from
n!>4*(n+1)*n^2, checked at 7 and then by induction. Hence these rational
examples have floor(d_(n+1)/d_n)=n+1 at every such index, with a positive
error O(n^3/n!) tending extremely rapidly to zero.

## What is NOT established

These denominators are not n!-1. Nor is it asserted that d_n+1 divides
d_(n+1)+1. The exact shifted-divisibility structure in the conjecture is
not preserved. This construction only excludes arguments using factorial
asymptotics, close-to-integer ratios, or the sign of their error alone.
It proves nothing about whether the target sum is rational.

Submission/Spec.lean remains unchanged with its original sorry.
