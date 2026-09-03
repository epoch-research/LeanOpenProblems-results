# Exact height reduction and the distinction from near row cancellation

Verified auxiliary work, NOT a settlement of Erdos 68. `Spec.lean`
remains unchanged with its original `sorry`.

`LambertAnnihilatorHeight.lean` compiles without warnings and has a built
olean. All five principal axiom audits use only `propext`,
`Classical.choice`, and `Quot.sound`.

## Exact division

For integer polynomials, put A_(B,d)(X)=B*X^d-1. If B>=1, c>=0, and

    c*|[X^j](A_(B,d)*V)| <= Q  for all j,

then `weighted_quotient_bound` proves

    c*(B-1)*|[X^j]V| <= Q  for all j.

Choose a coefficient of V of maximum absolute value. The coefficient
identity at the index d positions later and the triangle inequality give
B*max <= height(A*V)+max. This proves the stated bound without a degree
loss or a rational-division assumption.

Iterating gives `rowProduct_quotient_bound`: if

    P=(product_(d in ds)(d!*X^d-1))*V

has all coefficient absolute values at most Q, then every coefficient of
V, multiplied by product_(d in ds)(d!-1), has absolute value at most Q.
This assumes EXACT polynomial factorization.

## A verified limitation of a possible height extension

For d>=12 and N>=0, take

    W_N(X)=d!*X^d-1+X^(N+d+1).

Every coefficient has absolute value at most d!. Yet d!*X^d-1 does not
divide W_N: evaluation at x=1/(d!)^(1/d) gives x^(N+d+1)>0.

For the geometric row r_d(n), its response is exactly

    d!*r_d(n+d)-r_d(n)+r_d(n+N+d+1)
      =r_d(n+N+d+1)>0.

Writing lambda=(d!)^(1/d), its normalized magnitude is at most
2/lambda^(N+d+1), uniformly in n. This tends to zero as N grows.
Applying any fixed earlier raw row-cancelling operator multiplies this
upper bound by at most 2^(number of factors), so it still tends to zero.

`small_nondivisible_first_row` verifies the combined coefficient-height,
nondivisibility, and arbitrarily-small normalized-response statement.
Thus merely knowing that the first row is not exactly annihilated does
not extend the preceding degree-independent lower bound to height d!.

This does NOT prove failure of full-tail detection for these polynomials:
the next row can dominate their small first-row contribution. It also does
not rule out a more careful multi-row argument. No such argument compatible
with the required boundary integrality and smallness has been established.

The exact-division bound alone supplies no proof that a small full-target
combination has the necessary polynomial factors. The original conjecture
remains unproved and undisproved. No numerical experiment or submission
check was run, and nothing remains pending compilation.
