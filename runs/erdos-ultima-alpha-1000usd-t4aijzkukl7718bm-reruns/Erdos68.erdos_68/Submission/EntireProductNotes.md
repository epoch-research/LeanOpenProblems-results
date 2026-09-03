# Entire-product reformulation: no irrationality conclusion

These are mathematical development notes, not Lean-verified declarations.
No proof or disproof of the conjecture has been obtained.

Put

    f(z) = sum_(n>=2) z^n/(n!-z^n),
    H(z) = product_(n>=2) (1-z^n/n!),
    K(z) = sum_(n>=2) (z^n/n!) product_(k>=2, k!=n) (1-z^k/k!).

## Analytic and arithmetic properties

The product and the latter sum converge locally uniformly: on |z|<=R,
sum R^n/n! is finite, and product (1+R^n/n!) bounds the absolute products.
Thus H and K are entire. Off the zeros of H, K=H*f.

At z=1, all factors of H are positive and their deficits are summable,
so H(1)>0 and K(1)/H(1)=alpha, the target sum.

Both functions have integer factorial-scaled coefficients. More explicitly,
for a finite subset S of {2,3,...} with sum of elements m, its contribution
to H^(m)(0) is

    (-1)^|S| * m! / product_(k in S) k!.

The factorial quotient is an integer multinomial coefficient. Its contribution
to K^(m)(0) has the extra factor -|S|. At each degree only finitely many
subsets contribute.

Both functions satisfy maximum-modulus bounds exp(O(R^2)) as R tends to
infinity. To see a coarse sufficient bound, take M=ceil(2*e*R). For n<=M,

    log(1+R^n/n!) <= log(2) + max(0,n*log(e*R/n)) <= log(2)+R.

For n>M, R^n/n! <= 2^(-n). Hence log product (1+R^n/n!)=O(R^2).
For K, multiply this product bound by
sum (R^n/n!)/(1+R^n/n!) <= M+1.

## Why this does not settle the conjecture

If alpha=a/b were rational, with integer a and b!=0, then

    L(z)=b*K(z)-a*H(z)

would be an entire function of growth exp(O(R^2)), with integer
factorial-scaled coefficients and L(1)=0. These properties are compatible.
For example, (1-z)*exp(z^2) has all of them.

Even dividing out the zero gives no integrality contradiction. If
L(z)=sum l_n*z^n/n!, then the formal coefficients of L(z)/(1-z) are

    g_n = sum_(j=0)^n (n!/j!)*l_j,

which are integers. If L(1)=0, this quotient is entire and retains the same
order bound, using |1-z|>=R-1 on circles |z|=R>1.

Nor do the pole locations and factorial-scaled integrality alone force an
irrational value: (1-z)*f(z) has the same poles as f, integer factorial-scaled
coefficients, and value zero at 1. This comparison does not preserve f's
residues or coefficient positivity, and is not a counterexample to the
original conjecture; it only limits what the listed properties can prove.

A new argument exploiting further special structure would still be needed.
Submission/Spec.lean is unchanged and still contains its original sorry.

## Verified arithmetic of finite normalized pole cancellation

`PoleProductArithmetic.lean` now compiles without warnings and has an olean.
All three principal axiom audits list only propext, Classical.choice, and
Quot.sound. This remains an auxiliary result, not a settlement.

For N cancelled rows define the rational product value

    h_N = product_(n=2)^(N+1) (1-1/n!).

Its unreduced numerator product_(n=2)^(N+1)(n!-1) is odd. Reduction therefore
cannot cancel any power of two from the factorial-product denominator.
The file verifies

    2^(sum_(n=2)^(N+1) floor(n/2)) divides den(h_N).

More generally, the same power of two divides every natural multiplier C
for which C*h_N is an integer. Using Legendre's theorem, if M>0 and M!*h_N
is an integer, then

    sum_(n=2)^(N+1) floor(n/2) < M,
    N^2 < 4M.

Thus factorial clearing of this product value has a necessary quadratic
index cost, even after rational reduction. The result concerns the product
value itself and does not assume termwise clearing of its factors.

No claim is made that this arithmetic bound alone rules out every pole-
cancelling approximation: an analytic error lower bound, or a successful
alternative construction, would still be needed. In particular the bound
is not an irrationality proof. Spec.lean retains its original sorry.
