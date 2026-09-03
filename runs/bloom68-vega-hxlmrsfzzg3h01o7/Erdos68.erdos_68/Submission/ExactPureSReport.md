# Exact pure-S telescopers: positivity, matching, and primitive-height obstructions

## Outcome

No sequence of shrinking nonzero integer forms was obtained. In particular,
this report does **not** prove irrationality of

    S = sum_{n>=2} 1/(n!-1).

The calculations below stay in the proposed family, except for one explicitly
labelled comparison with denominator powers. They give:

* a nonvanishing congruence whose obstruction is independent of M;
* a finite, positive-coefficient recurrence for the inverse-factorial residual;
* uniqueness of full fixed-denominator matching at x=infinity;
* an obstruction to the natural coefficient cone based at t=1;
* an orbit-positive repair of the geometric truncation, together with a
  **primitive** 2-adic obstruction showing that this repaired family diverges;
* the exact exceptional diagonal left by primitive normalization of the
  unrepaired truncation;
* exact primal-and-dual certificates for four finite coefficient-cone optima;
* an explicit embedding showing why positivity-cone feasibility, without a
  primitive-height theorem, is not by itself an arithmetic advance.

All coefficient choices and finite certificates below are independent of any
assumption that S is irrational. `Submission/Spec.lean` was not edited.

## 1. Algebra and an M-independent nonvanishing obstruction

Write A_r(x)=(x+1)_r, H(x)=(x+r+1)(x+1)^(M-1), and

    P(x,t) = sum_{j=1}^M P_j(x)t^(M-j),
    U(x,t) = P(x,t)/(A_r(x)t^M),
    R(x,t) = c/(t-1) + U(x+1,(x+1)t) - U(x,t).

The proposed numerator is correct:

    N = c A_r H t^M + (t-1)[P(x+1,(x+1)t)-H P(x,t)],
    R = N / [(t-1) A_r H t^M].                                  (1)

The denominator is positive at all (n,n!), n>=2. Since deg P_j<=r,
U(n,n!) tends to zero and the sums converge absolutely. Thus

    sum_{n>=2} R(n,n!) = cS-U(2,2),
    D = 2^(M-1)(r+2)!,
    L = D sum R = Dc S-P(2,2).                                  (2)

For primitive normalization set

    g = gcd(|Dc|, |P(2,2)|),  q=Dc/g,  p=P(2,2)/g.

Then L/g=qS-p. Bounds for L and for L/g are different statements.

There is a useful simplification on the factorial orbit. Let

    B_n=P(n,n!),
    d_n=(n+r)!(n!)^(M-1).

Then U(n,n!)=B_n/d_n and d_(n+1)=H(n)d_n. Consequently

    R(n,n!) = [c d_(n+1) +(n!-1)(B_(n+1)-H(n)B_n)]
              /[(n!-1)d_(n+1)].                                (3)

For every n>=2,

    gcd(n!-1,(n+1)!)=1.                                        (4)

Indeed no prime <=n divides n!-1. The only remaining possible prime divisor
of (n+1)! is p=n+1; if p is prime, Wilson's theorem gives
(n!)-1 == -2 mod p, not zero. Here p>=3.

It follows that

    gcd(n!-1,d_(n+1)) = gcd(n!-1,(n+2)_r).                       (5)

Define

    m_(r,n) = (n!-1)/gcd(n!-1,(n+2)_r).

An exact zero R(n,n!)=0 therefore requires

    m_(r,n) | c.                                               (6)

This necessary divisibility condition is independent of M. In particular,
whenever

    n!-1 > |c|(n+2)_r,                                        (7)

the residual cannot be zero. Since factorial growth exceeds the fixed
polynomial on the right, (7) holds eventually. Thus **global nonnegativity
and c!=0 already imply infinitely many strictly positive residuals**. No
irrationality assumption or lattice avoidance argument is needed for that
implication. The difficult part remains simultaneous sign and smallness.

Prescribing zeros on a finite set I also forces

    lcm_{n in I} m_(r,n) | c.                                  (8)

For example, consecutive factorial-minus-one numbers are coprime. If both
R(K-1,(K-1)!) and R(K,K!) vanish, K>=3, then

    |c| >= [(K-1)!-1][K!-1] / [(K+1)_r (K+2)_r].               (9)

This is a useful exact height test for node-matching constructions, not a
no-go theorem for every possible cancellation scheme.

## 2. A finite positive recurrence for the raw inverse-factorial residual

Use z=x+1 and write

    h_j(x) = sum_{k>=0} 1/(x+1)_k^j
           = 1 + sum_{k>=1} a_(k,j)/(x+1)_k,
    C_k(y) = sum_j a_(k,j)y^j.

The product identity in the question and Tonelli give this expansion on the
positive domain in use. Each coefficient is a nonnegative integer; a_(k,j)=0
for j>k. Define

    q_(r,j)(x) = 1 + sum_{k=1}^r a_(k,j)/(x+1)_k.

Here is a finite recurrence which proves positivity of its residual, without
using a numerical tail estimate. For each j>=1 set Q_(0,j)(z)=1 and, for r>=1,

    a_(r,j) = [z^(j-1)] Q_(r-1,j)(z),
    Q_(r,j)(z) = (z+r)[Q_(r-1,j)(z)-a_(r,j)z^(j-1)] + a_(r,j).  (10)

Inductively deg Q_(r,j)<=j-1 and every coefficient is nonnegative: remove
the top-degree term, multiply the remaining polynomial by z+r, then add a
nonnegative constant. The exact identity is

    1-q_(r,j)(x)+q_(r,j)(x+1)/(x+1)^j
      = Q_(r,j)(z) / [(z)_(r+1) z^(j-1)].                     (11)

The recurrence follows by adding a_(r,j)/(z)_r to q_(r-1,j), and conversely
identifies the inverse-factorial coefficients. For example,

    C_1=y,
    C_2=y+y^2,
    C_3=y+y^2+y^3,
    C_4=y+3y^2+3y^3+y^4,
    C_5=y+10y^2+11y^3+6y^4+y^5.

In particular [y^r]C_r=1. For j=2 one gets

    Q_(1,2)=z+1, Q_(2,2)=z+3, Q_(3,2)=3z+10,
    Q_(4,2)=10z+43.

For the raw choice U_raw=sum_{j=1}^M q_(r,j)(x)t^(-j), c=1,

    R_raw = 1/[t^M(t-1)]
            + sum_{j=1}^M Q_(r,j)(z)/[(z)_(r+1)z^(j-1)t^j].    (12)

This is an exact positive residual on x>=2,t>1. Equivalently,

    N_raw = A_r H
            +(t-1) sum_{j=1}^M z^(M-j)Q_(r,j)(z)t^(M-j).       (13)

All coefficients of N_raw in x-2 and t-1 are nonnegative integers. This is
an actual finite polynomial positivity certificate, not just positivity of
an unnormalized approximation error.

## 3. Full matching with the prescribed denominator is unique

The polynomials

    (x+k+1)_(r-k),  k=0,...,r,

form a monic triangular Z-basis of the integer polynomials of degree <=r.
Thus an integer P_j/A_r has an integer inverse-factorial expansion of length
r, and no additional numerator freedom is hidden in a change of basis.

Suppose, for every j<=M, that one demands

    P_j(x)/A_r(x) - c h_j(x) = O(x^(-r-1)) as x->infinity.      (14)

Then P_j is uniquely forced to be

    P_j = c sum_{k=0}^{floor(r/j)} quo(A_r, A_k^j),             (15)

where quo is polynomial quotient. The divisors are monic, so (15) has integer
coefficients. Proof: multiply (14) by A_r. The numerator must be the
polynomial part of c A_r h_j. Terms with kj>r have zero polynomial part.
Equivalently, (15) is exactly c A_r q_(r,j).

Consequently full fixed-denominator matching at infinity reproduces the raw
truncation. It is not a new Padé degree of freedom. This conclusion does not
exclude partial matching, matching at factorial nodes, or a genuinely
variable denominator.

## 4. Quantitative obstructions for the raw truncation

### 4.1 The geometric obstruction and the h_2 obstruction

For r>=2,M>=2, the raw boundary error has two disjoint positive pieces:

    S-U_raw(2,2) >= 2^(-M) + 1/[6r(r+1)(r+2)].                (16)

The first term is the omitted k=0 geometric series. For the second, the
single summand 1/(x+1)^2 in h_2 supplies

    a_(k,2) >= (k-2)!.

At x=2 its inverse-factorial tail is exactly

    sum_{k>r} (k-2)!/(3)_k = 2/[3r(r+1)(r+2)].                (17)

Multiplication by y^2=1/4 gives (16). Hence for the raw integer form,

    D sum R_raw >= (r+2)!/2 + 2^(M-1)(r-1)!/6.                (18)

A common integer scaling c>0 multiplies the right side by c. Even omitting
the h_2 term, the raw unprimitive forms cannot shrink for any choice of M.

When M>=r, define the geometric-tail-corrected boundary value

    B_r = 1 + sum_{k=1}^r C_k(1/2)/(3)_k.

Then

    U_raw(2,2)=B_r-2^(-M),  B_r increasing to S.               (19)

There is a stronger exact lower bound for S-B_r from the first nontrivial
summand y/(x+1-y) in F. Its inverse-factorial coefficients are
[y(y)_(k-1)], so

    S-B_r >= (1/5)(1/2)_r/(3)_r
           = 2 binom(2r,r)/[5*4^r(r+1)(r+2)].                 (20)

This is asymptotic to 2/(5 sqrt(pi)) r^(-5/2), and in particular is only
polynomially small. The asymptotic is not needed for the exact bounds.

### 4.2 An orbit-positive repair, ruled out even primitively

The k=0 geometric defect can be removed within the exact family. Set

    U_hat = U_raw + t^(-M),

i.e. replace P_M by P_M+A_r. Then

    R_hat = R_raw - (1-z^(-M))t^(-M).                         (21)

Assume M>=r and choose M large enough that

    6^M >= (r+4)!,    4^M >= r+5.                            (22)

These conditions hold, for example, for all sufficiently large M for each r.
They prove R_hat(n,n!)>0 for every n>=2:

* at n=2, the geometric term in (12), minus the correction in (21),
  is exactly 6^(-M)>0;
* at n>=3, the j=1 term in (12) dominates t^(-M) whenever
  t^(M-1)>=(n+1)_(r+1). At n=3 this is the first inequality in (22).
  The ratio of the left/right quantity at n+1 to that at n is
  (n+1)^M/(n+r+2), at least one by the second inequality in (22).
  The other terms left in (12) are positive.

Thus this is a genuine parametric, strictly positive family, with

    U_hat(2,2)=B_r.                                          (23)

It is not rectangle-positive in all independent x,t>=2: for x->infinity
and fixed t>2 its residual tends to (2-t)/[t^M(t-1)]<0. Its positivity really
uses t=n!, as allowed by the question.

Nevertheless it fails **after full primitive reduction**. Put

    A=(r+2)!/2,   D0=2^r A,   a=v_2(A).

Write B_r=1+T_r/D0. The integer T_r is odd. Indeed, in the common numerator,
all k<r contributions have a factor 2, while the k=r contribution is odd
because [y^r]C_r=1. Therefore the reduced denominator q_r of B_r satisfies

    v_2(q_r)=r+a.                                            (24)

For r>=2 the primitive form J_r=q_r S-p_r consequently obeys

    J_r >= 2^(r+a)/[6r(r+1)(r+2)] -> infinity.                (25)

This is not an artifact of keeping D instead of gcd-reducing it. Enlarging M
merely introduces powers of two which cancel from the boundary; (24) remains.
Common scaling of c and P likewise cannot help. A fixed geometric-tail repair
of this form therefore does not solve the problem.

### 4.3 The exceptional primitive diagonal for the unrepaired truncation

One must not overstate (18) as a universal primitive obstruction. Let

    K_r = r+v_2((r+2)!/2).

For M>=r and M!=K_r, subtracting 2^(-M) from B_r cannot cancel the larger
2-adic denominator. Thus the reduced denominator q_(r,M) of the raw boundary
satisfies

    v_2(q_(r,M))=max(M,K_r).

Together with its 2^(-M) error, this proves

    q_(r,M)(S-U_raw(2,2)) > 1.                               (26)

There is exactly one possible exception per r in this range: M=K_r. Write
A=2^a A_odd and B_r=1+T_r/(2^r A). On that diagonal the exact denominator is

    q_(r,K_r) = 2^r A / gcd(2^r A, T_r-A_odd).                (27)

No general sufficiently strong gcd estimate for (27) was proved here. For
example r=2,M=4 gives the primitive form 6S-7, so one really cannot silently
remove the exceptional case. The recurrence

    T_r=2(r+2)T_(r-1)+2^r C_r(1/2), T_0=0,

computes (27) exactly. Checks through r=80 show huge denominators at larger
r, but they are not a parametric theorem. By (20), shrinking on this diagonal
would require q_(r,K_r)=o(r^(5/2)), an almost-total cancellation of the
factorial boundary denominator. The range M<r and more general cancellations
are also not excluded by (26).

## 5. What exact coefficient cones do and do not establish

### The cone at t=1 has a universal unprimitive obstruction

Suppose all coefficients of N in X=x-2 and T=t-1 are nonnegative. Since

    N(2,1)=c A_r(2)H(2),

this forces c>0 and

    N(2,2)>=N(2,1),
    R(2,2)>=c/2^M,
    D sum R >= c(r+2)!/2.                                   (28)

This applies to the entire cone, not just the raw recurrence. An expansion
with nonnegative coefficients in x-2 and t itself has the same obstruction.
Thus that natural cone cannot deliver the requested unprimitive D sum R->0.

### The cone at t=2 avoids (28), but has a necessary height condition

Now suppose all coefficients in X=x-2 and T=t-2 are nonnegative. At fixed
x>=2 the coefficients in T are nonnegative. For t>=3,

    N(x,t)>=sum_j coefficient_j(x)>=|N(x,1)|=|c| A_r(x)H(x).

In particular, since 3!=6,

    D sum R >= D R(3,6)
             >= |c|(r+2)!/[10*3^M].                         (29)

So unprimitive shrinking in this cone requires

    3^M / (|c|(r+2)!) -> infinity.                           (30)

This is only necessary, not sufficient. It already excludes M=O(r), even
with |c|=1, as r grows. Dividing by g changes the necessary bound to
|q|/(5*6^M), so primitive optimization must be tracked separately.

### Exact finite LP certificates

The search used a rational objective, maximize P(2,2)/D with c=1, under
coefficient inequalities for N(X+2,T+2). No numerical value of S entered the
optimization. Floating-point LP selected active constraints; the saved
vertices and duals were then checked exactly over Q, and the resulting
integer coefficients and primitive boundary gcds were checked over Z.

Four independently rechecked ratio optima are:

| r,M | primitive q,p | exact interval for qS-p |
|---|---|---|
| 1,3 | 23902, 29677 | (284,285) |
| 1,4 | 490845032448, 614212524137 | (1061113278,1061113279) |
| 2,3 | 13365373320, 16655736559 | (97742267,97742268) |
| 3,4 | 607507146212595927987200, 760990223981341193035051 | (519227874977504054631,519227874977504054632) |

For example r=1,M=3 uses c=131461 and, in X=x-2,

    P_1=560439+124542X,
    P_2=37740+166056X,
    P_3=1600128-39420X.

Its D is 24 and its boundary gcd is 132. The primitive form is therefore
23902S-29677, not a small form. These calculations demonstrate actual height
loss at ratio-optimal vertices; they do not prove a no-go theorem for all
interior points or for primitive-height optimization.

### Why cone feasibility alone is universal after primitive reduction

There is an exact embedding worth making explicit. Take any coprime positive
integers a,q with a/q<S. Because the raw rational bounds tend to S, choose
r,M and a raw integer numerator P0 with

    b=P0(2,2),   b/D>a/q.

Set

    c=q b,   P=a D P0.                                      (31)

Then

    N(c,P) = aD N_raw + (qb-aD) A_r H t^M.                   (32)

Every coefficient in x-2,t-1 is nonnegative. But its boundary is

    L=Db(qS-a),
    gcd(Dc,P(2,2))=Db,

so its primitive form is exactly qS-a. This uses no irrationality assumption:
it embeds any independently certified rational lower bound.

Consequently the union of even the stronger t=1 coefficient cones contains
**every** positive lower rational approximation after primitive reduction.
A finite feasible cone point or an improving real-valued LP objective is
therefore not the missing arithmetic ingredient. A successful parametric
argument must prove useful primitive heights as well as closeness; using an
already-good approximation to select (31) merely transfers the original
problem into the cone.

## 6. A finite pure-S check, not a shrinking sequence

The repaired family gives a compact independent check entirely in the exact
ansatz. For r=5,M=8, conditions (22) hold, and

    B_5=11203/8960 > 5/4.

Let P_hat be the integer numerator from Section 4.2, and choose

    c=11203,  P=11200 P_hat.

Its residual is

    3/(t-1)+11200 R_hat,

so it is strictly positive at every factorial node. Its primitive boundary
form is exactly 4S-5. An exact rational tail bound verifies

    0 < 4S-5 < 1/71.                                       (33)

This is only a finite sanity check of positivity, normalization, and primitive
reduction. It is not a new shrinking sequence and is not used as evidence of
irrationality.

## 7. Height-aware tail certification and denominator-power comparison

Write P_j(x)=sum_{k=0}^r p_(j,k)x^k and define

    H_P=sum_{j,k}|p_(j,k)|.

For n>=2, A_r(n)>=n^r gives |U(n,n!)|<=H_P/n!. Since the factorial-minus-one
summands satisfy a_(n+1)/a_n<1/(n+1), a rational bound for any N>=2 is

    beta_N=(N+2)/[(N+1)((N+1)!-1)],
    0<sum_{n>N}1/(n!-1)<beta_N.

Telescoping the residual tail gives the height-aware estimate

    |sum_{n>N}R(n,n!)|
       <= |c| beta_N + H_P/(N+1)!.                          (34)

If all residuals are nonnegative, multiply (34) by D/g and add the exact
finite residual sum to obtain an upper certificate for the primitive form.
This keeps both c and P heights explicit. Merely bounding 1/n! without H_P
can be arbitrarily misleading for a Padé or interpolation construction.

For comparison only, allowing A_r(x)^M as a denominator makes the direct
rectangular truncation

    V=sum_{k=0}^r sum_{j=1}^M [A_k(x)t]^(-j)

available. Its exact residual is positive:

    1/[t^M(t-1)] + sum_{j=1}^M [A_(r+1)(x)t]^(-j).

But its natural boundary denominator is ((r+2)!)^M, and the n=2 geometric
error alone gives normalized error at least

    ((r+2)!/2)^M.

Thus merely replacing the simple denominator by powers does not fix the
normalization problem. This observation does not exclude a genuine Padé
construction with those powers and nontrivial cancellation.

## 8. Verification and remaining problem

New files:

* `Submission/ExactPureSReport.md`;
* `Submission/exact_pures_verify.py`;
* `Submission/exact_pures_cone_certificates.json`.

The exploratory cone builder and additional output are in
`/tmp/erdos68_exact_pureS/`. The standalone verifier uses exact integer and
rational arithmetic, not a floating-point test of positivity. Run:

    python3 Submission/exact_pures_verify.py

Verified items include the numerator/orbit/boundary identities, 64 matching
and Q-recurrence cases, 25 raw numerator coefficient certificates, C_r and
primitive denominator formulas through r=80, 2607 gcd checks, the explicit
orbit-positive repair and (33), and exact primal plus dual certificates for
the four displayed LP vertices. Infinite positivity and the parametric
obstructions are proved above; they are not inferred from the finite tests.
No Lean formalization of the new results is claimed.

`Spec.lean` has unchanged SHA-256:

    c5c794ec0dcb35e079f78ce20043053fe0bf048aa47873395df7221ce5aea20d

What remains is a parametrically controlled cancellation with

    N(n,n!)>=0 for all n>=2,
    (D/g) sum R(n,n!) -> 0

(or the stronger unprimitive condition requested in the question), with
c!=0 and a proved primitive-height estimate. Nonvanishing would then follow
automatically from (6)-(7). Full x-infinity matching, the t=1 coefficient
cone, and the simple orbit-positive raw repair do not supply such a family.
General factorial-node positivity, partial matching, the exceptional gcd
problem (27), and more sophisticated denominators remain unresolved here.
