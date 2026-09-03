# Testing position-dependent digit constraints

This work does NOT settle Erdős 773. `Spec.lean` has not been changed in this
session: it still has the same conjecture and one admission at line 2031.

## Current finite construction

`PositionDigitObstacle.lean` uses B=1152*(t+18) and four degree-48 words.
The nine digit values are

    0, 1, 21, 219, 309, 1920, 4224, 45*(t+18), 99*(t+18).

A finite pattern certificate asserts that every digit label has the same
number of occurrences AND the same sum of positions in all four words.
Consequently, for EVERY function f from digits to integers, both

    sum_i f(d_i),      sum_i i*f(d_i)

agree across the words. This includes ordinary and first-position-weighted
digit sums and squared-digit sums, as well as the complete histogram.
The words have leading digit 1, all lower digits divisible by 3, and constant
digits congruent to 3 modulo 9. The common digit sum is

    15361 + B/4 < B.

Every digit is less than B/2. The evaluated squares collide nontrivially.
At t=0 the root gcd is 15; at t=1 it is 3. Do NOT claim gcd 3 at t=0.

The construction is exact, from

    U(X)=1+X+X^2+X^3,
    V(X)=1-X-X^2+X^3,
    Q(X)=X^4 + U(X)/16 + 3*i*V(X)/128,
    R(X)=X^20 + 3072*U(X^5) + 1152*i*V(X^5).

Take real and imaginary parts of (1+i)*Q*R and (1+i)*conj(Q)*R, substitute X^2,
and move the small fractional coefficients 5/128 and 11/128 into empty
preceding positions as digits 5*B/128 and 11*B/128. The identity of squared
norms is preserved at the chosen integer base.

## Completed Lean verification

The entire `PositionDigitObstacle.lean` file now compiles with

    lake env lean -s 65536 Submission/PositionDigitObstacle.lean

All seven printed audits (statistics, leading, constant_mod, lower_divisible,
digit_sum_lt_base, not_sidon, primitive_example) use only the permitted axioms.
The log is /tmp/position-digit.log. Temporary prefix/debug files were removed.

Technical fixes:
* The alphabet is a Nat pattern match, rather than a nested Fin vector whose
  numeric lookups were not simplifying inside large expressions.
* The natural-number value expansion is proved separately before casting to
  integers. Expanding the finite sums under casts directly timed out.
* A four-variable norm identity is combined with four linear encoding
  identities, rather than expanding a degree-96 identity in the parameter t.
* Keeping the base opaque and using 1152*(t+18)=B avoids huge coefficients.
* The primitive example is t=1, not t=0.

`Spec.lean` is unchanged (SHA-256
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14).
It still has exactly one admission, at line 2031, for 0 < epsilon <= 1/3.
No submission call has been made.

## General mathematical extension (not yet formalized)

For any k>=1, set m=2^k, L=m+1, K=96*m, and

    U(X)=sum_{j=0}^{m-1} X^j,
    V(X)=product_{r=0}^{k-1} (1-X^(2^r)),
    Q(X)=X^m + (24/K)*U(X) + i*(9/K)*V(X),
    R(X)=X^(m*L) + 8*K*U(X^L) + i*3*K*V(X^L).

The coefficients of V are the +/-1 Thue–Morse signs and its first k jets at
1 vanish. The same norm construction and X^2 substitution give degree
2*m*(m+2) digit words. Their integer digit values are 21, 219, 309 in the
product blocks, 5*K and 11*K in the R blocks, 15*B/K and 33*B/K in the shifted
Q blocks, and a common leading 1.

For each polynomial position weight of degree <k and EVERY digit function f,
the weighted f-statistics agree. To see this, expand each position weight in
the two block coordinates. The Thue–Morse signs have zero moments of every
order <k in each coordinate. Thus flipping either sign leaves all the weighted
digit counts unchanged.

The common sum is 1+960*m^2+B/4. Taking B=1536*m^2*(u+1) makes it less than B,
with all digits less than B/2. All lower digits are divisible by 3 and all
constant digits are 3 modulo 9.

This suggests that no FIXED finite collection of polynomial position-weighted
digit statistics repairs the construction. It does NOT address constraints
whose number grows quickly with the word degree, and it does not prove that
every large statistic class has a collision.

## Main-gap research this session

Gaussian factorization organizes the collisions but does not provide a
near-linear independent subset. Recursive modular Sidon lifting loses a
power-sized density factor. Generic hypergraph bounds stay at exponent 2/3.
No valid argument for either the conjecture or its negation has emerged.

## Entropy caution about complete histogram classes

A full histogram is not a cheap constraint in the small-total-sum regime. If
a word has digit sum <B and r distinct digit values, then
r*(r-1)/2 < B: the distinct nonnegative values already have at least that
sum. Consequently a fixed histogram class of length d has size at most
r^d <= (1+sqrt(2*B))^d. For roots of size about B^d this is only a
1/2+o(1) exponent as B grows. The full-histogram counterexamples are useful
because they simultaneously refute many FEWER-statistic candidates, not
because fixing a whole histogram could itself yield a near-linear class.
