# Toeplitz restriction investigation

**Status: not a proof or disproof of `Spec.lean`.** The target file is unchanged.
The results below are hand mathematics, not Lean formalizations. The missing
AP-specific estimate is identified explicitly in section 6.

## 1. Exact interval testing, with no coefficient loss

Fix beta >= 0 and set

    L(t) = (log log(e^e+t))^beta,
    w(d) = L(d)/d,                       d >= 1.

For a finite integer set A, let H_A have zero diagonal and off-diagonal
entries w(|a-b|). Use **ordered-pair** energy

    E(F) = sum_{a != b in F} w(|a-b|),
    V(A) = sup_{intervals I, A cap I nonempty} E(A cap I)/|A cap I|.

Then

    V(A) <= ||H_A|| <= C_beta (1+V(A)).                 (1)

In particular, uniform normalized energy bounds over the hereditary family
of all k-AP-free sets are equivalent to uniform operator bounds. Arbitrary
coefficients do not create an extra log|A| loss in this family statement.

### Proof

Put b_j=2^(-j)L(2^j), D=sum_{j>=0} b_j, and

    K(d) = sum_{j>=0} b_j (1-|d|/2^j)_+.

Here D<infinity, K(0)=D, and, for d>=1,

    w(d)/8 <= K(d) <= sum_{2^j>d} b_j <= B_beta w(d).   (2)

For the lower bound choose 2d<=2^j<4d. The upper bound follows from the
geometric tail and L(2^(s+r))/L(2^s)<=C_beta(1+r)^beta.

Fix a translated dyadic grid, truncated at a largest scale. Set
mu(I)=|A cap I| and alpha_I=b_j mu(I)^2 when |I|=2^j. For every grid interval
J, expanding the squares and summing over pairs gives

    sum_{I subset J} alpha_I
      <= D mu(J) + B_beta E(A cap J)
      <= (D+B_beta V(A)) mu(J).                        (3)

The scalar dyadic Carleson embedding therefore gives

    sum_I b_log2|I| |sum_{a in A cap I} c_a|^2
      <= 4(D+B_beta V(A)) sum_A |c_a|^2.               (4)

This embedding needs no doubling assumption on the atomic measure mu.
Indeed, maximal intervals with average |c|>t and (3), followed by layer cake,
bound its left side by (D+B_beta V(A))||M_mu c||_2^2. The dyadic maximal
inequality ||M_mu c||_2<=2||c||_2 follows from

t mu{M_mu c>t} <= integral_{M_mu c>t}|c| dmu

by integration and Cauchy--Schwarz.

Average (4) over all integer translations modulo the largest dyadic scale.
A pair at distance d shares a length-2^j interval with probability
(1-d/2^j)_+. Thus the averaged quadratic form has the truncated K kernel.
Letting the truncation grow proves ||K_A||<=4(D+B_beta V(A)). Finally,

    |<H_A c,c>| <= <H_A |c|,|c|> <= 8<K_A |c|,|c|>.

This proves the upper half of (1). Testing indicator vectors proves the
lower half. The comparison in (2) is entrywise, not a Loewner comparison;
taking absolute values is essential.

## 2. The Fourier weight and its sufficient density rate

Let F_R(t)=R^(-1)|sum_{u=0}^{R-1}e(ut)|^2 be the Fejer kernel. The integrable
nonnegative weight

    W_beta(t)=sum_{j>=0} b_j F_(2^j)(t)

has Fourier coefficients K(d). If delta=dist(t,Z) and u=log(1/delta), then

    W_beta(t) comparable_beta (1+u)[log(e+u)]^beta.      (5)

The scales 2^j delta bounded by a small constant each contribute comparable
to L(2^j). Their sum is comparable to u(log u)^beta. The remaining scales
are bounded using F_R(t)<=C/(R delta^2).

Thus (1) is also an exact localized weighted restriction problem:

    integral_T W_beta(t)|sum_A c_a e(at)|^2 dt
      <= C sum_A |c_a|^2.                              (6)

For A in an interval of length N, m=|A|, its constant-coefficient Fourier
polynomial has modulus >=m/2 on an arc of length comparable to 1/N, after
a harmless frequency translation. Equations (2) and (5) give

    E(A)/m >= c_beta (m/N) log(2+N)L(N)-C_beta.          (7)

The additive constant is needed, for instance for a singleton. Consequently
a uniform bound in (1) or on E(A)/|A| over k-free sets would imply

    r_k(N) <= C_(k,beta) N/[log(2+N)L(N)].              (8)

For beta>1, the resulting dyadic density series is bounded by
sum_j 1/[j(log j)^beta], hence converges. This would settle the target if
proved for every fixed k. The smaller bump

    L(d)=log log d (log log log d)^(1+epsilon)

(with positive small-d modifications) is also sufficient.

A useful reverse sufficient condition is the row/Schur estimate

    sup_{A k-free} ||H_A||
      <= C_beta sum_j [r_k(2^j)/2^j] [log(e+j)]^beta.   (9)

The two distance shells around a fixed point are translated/reflected
k-free subsets of intervals of length 2^j. Bloom--Sisask's proved
r_3(N)<=C N/(log N)^(1+c) therefore gives (6) for k=3 and every fixed beta.
This uses their deep theorem, not a new proof of it.

## 3. Global Orlicz improvement is false on one 3-free spectrum

Let C be the nonnegative integers with ternary digits in {0,1}, and let
C_n consist of its first n digits. These are globally 3-AP-free: in
x+z=2y all ternary digit sums are at most 2, so equality is coordinatewise
and forces x=y=z. Define

    f_n(t)=2^(-n/2) sum_{a in C_n} e(at)
          =prod_{j<n}(1+e(3^j t))/sqrt(2).

Then ||f_n||_2=1, but

    ||f_n||_1 <= (2 sqrt(2)/3)^n.                       (10)

Here is an elementary proof of (10). Set phi(t)=sqrt(1+cos(2pi t)). Under
the map t -> 3t mod 1, the average of phi over the three preimages of u is
at most 2sqrt(2)/3. Indeed, with v=pi(u+1)/3 in [pi/3,2pi/3], that average
is

    (sqrt(2)/3)(sqrt(3) sin v + |cos v|) <= 2sqrt(2)/3.

The factors phi(3^j t), j>=1, are constant on these three preimages.
Integrating the first factor and repeating proves (10).

Thus f_n tends to zero in measure, although its squared L2 norms remain 1.
For every Young function Phi with Phi(s)/s^2 -> infinity, a uniform bound
on the L^Phi norms would make |f_n|^2 uniformly integrable and contradict
this fact. In particular, even L2 log L restriction fails, as does every
fixed slower strong superquadratic Orlicz gain.

Nevertheless the desired localized Toeplitz operators on these SAME sets
are uniformly bounded for every beta. With alpha=log_3 2<1,

    |C cap I| <= C |I|^alpha

for all intervals of length >=1, by ternary-block counting. Hence the row
sums are bounded by

    C_beta sum_{j>=0} 2^(-(1-alpha)j)[log(e+j)]^beta.

Global rearrangement-invariant Fourier gains are therefore substantially
stronger than, and cannot be substituted for, (6).

## 4. Arithmetic-chart aggregation obstructions

On a finite A define

    T_q(A)(a,b)=q/|a-b| if a!=b and q divides a-b,
               0 otherwise.

If H_0 is uniformly bounded on all k-free sets, then T_q is also uniformly
bounded, by decomposing A into residue classes and affinely compressing.
Even the elementary ternary cubes above have these bounds uniformly in q:
write q=3^t u with 3 not dividing u. In each compressed residue class,
modulo 3^j there are at most 2^j possible residues, since multiplication
by u is invertible modulo 3^j. This gives the same interval exponent alpha
and a uniform Schur bound.

Two facts prevent naive aggregation of these separate chart bounds.

### 4.1 Positive global direction weights cannot dominate a bump

The difference set C_n-C_n is the ENTIRE integer interval
[-(3^n-1)/2,(3^n-1)/2], by balanced ternary. Suppose L(d) is nondecreasing
and unbounded, and adaptive nonnegative coefficients lambda_q(A) satisfy
sum_q lambda_q(A)<=B and entrywise off-diagonal domination

    H_L(A) <= sum_q lambda_q(A) T_q(A).

At a prime distance p present in C_n this requires

    lambda_1 + p lambda_p >= L(p).

Thus B>=sum_{p<=(3^n-1)/2}(L(p)-B)_+/p, contradicting divergence of the
prime reciprocal sum as n grows. Coefficients depending arbitrarily on A
do not repair this. Adding a diagonal constant does not repair it either.

### 4.2 No generic l^p saving across directions

For j<n the distance-3^j pairs in C_n form a perfect matching (flip digit
j). Its adjacency matrix is entrywise below T_(3^j) and fixes the positive
constant unit vector v. Therefore

    ||sum_{j<n} c_j T_(3^j)(C_n)|| >= sum_{j<n} c_j

for c_j>=0. Since the separate norms are bounded, l1 aggregation is sharp;
no uniform replacement by an l^p norm, p>1, is possible.

More exactly, let r_n(d)=#{(a,b) in C_n^2:a-b=d}. It equals 2 to the number
of zero balanced-ternary digits of d. If e_q=<T_q v,v>, then e_q>=2r_n(q)/2^n,
and, for every finite s>=1,

    sum_q e_q^s >= 2^(s-1)[(1+2^(1-s))^n-1].

A successful method must use joint local overlap and exact AP compatibility,
not just globally weighted separate chart estimates.

## 5. Fractional Carleson self-improvement is also false

This section is explicitly a FRACTIONAL countermodel, not an AP-free set.
Fix 0<epsilon<=1/2. Allow finite atomic measures on distinct integers whose
decreasing atom weights satisfy

    mu*_j <= epsilon/(1+log j).

This class is closed under restrictions, decreasing weights and every
injective relocation. In particular it is closed under all affine and
Freiman-isomorphic charts. It satisfies every fractional AP-edge constraint
sum_{x in P} mu(x)<=k epsilon<=k-1, for k>=3. It does not satisfy the exact
0--1 exclusion of a fully occupied AP.

For nonnegative finitely supported u at distinct integers, one has

    sum_{x!=y} u(x)u(y)/|x-y|
      <= C sum_j (1+log j)(u*_j)^2.                    (11)

To prove this, divide ranks into blocks [2^r,2^(r+1)) and put
v_r=u*_(2^r). For r<=s, the sum of 1/|x-y| between the two rank blocks is
at most C 2^r(s+1): around each x at most two integers have each distance.
With a_r=2^(r/2)sqrt(r+1)v_r, the resulting quadratic form is bounded by
the summable convolution kernel

    2^(-|r-s|/2)sqrt(1+|r-s|).

Monotonicity of u* bounds sum_r a_r^2 by the right side of (11), using the
preceding rank block.

Rearrangement also gives

    sum_x u(x)^2/mu(x)
      >= sum_j (u*_j)^2/mu*_j
      >= epsilon^(-1) sum_j (1+log j)(u*_j)^2.

Apply this to u=sqrt(mu)|f|. The weighted endpoint matrix
sqrt(mu(x)mu(y))/|x-y| has norm at most C epsilon, uniformly in every
placement and every coefficient vector. Its positive completion with kernel
1/(1+|x-y|) has the same bound; that kernel is positive definite because
it is the integral of t^|x-y| over 0<=t<=1.

Nevertheless mu(n)=epsilon/(1+log n) has divergent reciprocal mass
sum_n mu(n)/n. For ANY nondecreasing unbounded L, testing on [N/2,N] and
using distances sqrt(N)<=d<=N/4 gives

    ||sqrt(mu(x)mu(y)) L(|x-y|)/|x-y||| >= c epsilon L(sqrt(N)).

So no unbounded bump follows from these fractional endpoint bounds, even
with arbitrary injective-chart closure.

The same measures satisfy all separate dyadic Carleson conditions

    sum_{I subset J} mu(I)^2/|I| <= C epsilon mu(J)

in every chart. John--Nirenberg controls the potential variable, not the
number of occupied scales. Concretely, put N=2^l and give every point in
[0,N) weight delta=epsilon/(l+1). For the standard dyadic tree, the potential
sum_{I subset J}(mu(I)/|I|)1_I equals epsilon identically. All of its moments
are bounded, but weighting level j by [log(j+2)]^beta makes it comparable
to epsilon(log l)^beta, which diverges.

An open Riesz-order improvement is impossible even on integral 3-free sets:
for any 0<eta<1, Behrend sets with size N exp(-C sqrt(log N)) give norm at
least (|A|-1)N^(-1+eta) for the kernel d^(-1+eta), tending to infinity.
This does not rule out a logarithmic bump.

## 6. Exact remaining obligation and scope

No proof of (1) uniformly over all k-AP-free A at a sufficient beta>1 has
been obtained for arbitrary k. Equivalently, the missing statement is an
AP-specific budget of the form

    sum_{I subset J} [log(log2|I|+2)]^beta
                       |A cap I|^2/|I|
      <= C_k |A cap J|.

The separate arithmetic-chart endpoint tests, global Orlicz restriction,
generic cross-direction orthogonality, and fractional Carleson
self-improvement cannot establish it by the shortcuts refuted above.
These are barriers to proof strategies, NOT a disproof of Erdos--Turan.

A useful caution about seeking an integral countermodel: any hereditary
integer-set class closed under affine compression and having uniform H_0
norm <=C automatically excludes every sufficiently long AP, since an
m-AP compresses to [m], whose ordered mean energy is

    2 H_(m-1)-2(m-1)/m >= 2 log m-2.

An actual such class with unbounded reciprocal sums would therefore already
produce a fixed-length Erdos--Turan counterexample. None has been found.

Sources checked: Bloom--Sisask, /corpus/src/2007.03528/Roth.tex, lines 26--46;
Ryou's Orlicz Lambda paper, /corpus/src/2110.07135/2110.07135.tex;
Kerman--Sawyer background, /corpus/src/1811.05112/1811.05112.tex, lines 98--107;
classical Dirichlet-capacity scope, /corpus/src/1008.5342/1008.5342.tex,
lines 280--348. The discrete Carleson argument and explicit obstructions
above have been checked directly rather than inferred from these references.
