# Phase-averaged Lambert tails (unresolved)

This is informal mathematical analysis, not a Lean theorem or a settlement.
`Spec.lean` is unchanged with its original `sorry`. No complete proof or
disproof has been found or submitted in this continuation.

For d>=2, write B=d!, rho=1/B, and for n>=0 write n=q*d+r, 0<=r<d.
Averaging the d phases of a geometric Lambert row gives

    u_d(n) = (1/d) sum_(h=0)^(d-1) B^(-floor((n+h)/d))
           = rho^q * (1-r/d+r*rho/d).

Extend u_d evenly to integer arguments. It is a positive-definite sequence.
An elementary positive expansion, with G_l(n)=max(0,l-|n|), is

    u_d(n) = sum_(k>=1) [(1-rho)^2*rho^(k-1)/d] * G_(kd)(n).

For fixed n the identity follows by summing the geometric and weighted
geometric tails. Each G_l is a Gram kernel: it is the overlap size of two
integer intervals of length l. Consequently

    K(n) = sum_(d>=2) u_d(n)/(d!-1)

is positive definite and K(0)=alpha. All these sums converge absolutely;
0<=u_d(n)<=1 suffices for the sum over d.

## The additional constant in its off-diagonal entries

Put

    gamma = sum_(d>=2) 1/(d*d!).

For 0<=n<=d one has exactly

    u_d(n)/(B-1) = 1/(B-1) - n/(d*B).

Thus for each fixed n,

    K(n) = alpha - n*gamma + R_n,

where R_n is the finite rational correction

    R_n = sum_(2<=d<n)
          [u_d(n)/(d!-1)-1/(d!-1)+n/(d*d!)].

It would be invalid to call these off-diagonal entries rational merely
under rationality of alpha: gamma is a separate constant.

For finitely supported integer weights w_i, with S=sum_i w_i, the exact
quadratic form is

    sum_(i,j) w_i*w_j*K(i-j)
      = S^2*alpha - gamma*sum_(i,j) w_i*w_j*|i-j|
                    + sum_(i,j) w_i*w_j*R_|i-j|.

The gamma term can be removed by the explicit isotropy constraint
sum_(i,j) w_i*w_j*|i-j|=0. For example w=(1,-1,1) satisfies it. This leaves
a positive form in alpha with a rational boundary, not an automatically
integral boundary. No useful bound on its primitive integer normalization
was obtained.

## An elementary lower bound before normalization

The triangular-kernel expansion gives a stronger bound than positivity
for integer weights. If S=sum_i w_i, then

    sum_(i,j) w_i*w_j*G_l(i-j) >= l*|S|.

Indeed the left side is the sum of squares of all length-l window sums.
Those window sums are integers and have total l*S. For an integer z,
z^2>=|z|, and the triangle inequality proves the bound. Summing the positive
triangular expansions therefore gives

    sum_(i,j) w_i*w_j*K(i-j) >= |S|*alpha.

This does not exclude small errors AFTER dividing a coefficient pair by
its gcd. It must not be promoted to a primitive-pair lower bound without
controlling that division. No such control was established here.

## Other arithmetic review

The actual carry's predecessor and prime-unit conditions were reviewed
alongside the original Dold congruences. Preserving additional congruences
by changing the carry modulus enlarges the tail intervals. No construction
retaining both the extra congruences and the bounds needed for a
contradiction was obtained. The established rationality-forced prime-gap
pattern has not been contradicted for the exact target.

No numerical search was run, no new Lean declaration was added, and no
computation or compilation is pending. There is no complete informal proof
awaiting formalization.
