# Periodic Gaussian masks: audited local inequality and actual norm asymptotic

## Verdict and precise theorem

**The proposed fixed-modulus theorem is valid, unconditionally.** The local
fiber-gap argument preserves all correlations. Global saturation requires an
additional argument, supplied below: sufficiently many split-prime orientation
switches realize every locally admissible residue, for almost every sum of two
squares. It does **not** assert representation of every admissible integer.

Write O=Z[i], N(z)=z conjugate(z), let S be the positive integers represented by
N, put S(X)=|S intersect [1,X]|, and let kappa be the Landau--Ramanujan constant.
Fix M>=1 and a nonempty A subset O/(M). Set

    delta=|A|/M^2,   B=A-A,   P_R=(A+MO) intersect closedDisk(0,R),
    F_B(X)=#{m<=X : m>0, m=N(z) for some z in O with z mod M in B}.

Use the local measure mu in Section 1 and put

    T_B = N({z in product_(p|M) O_p : z mod M in B}),
    lambda_B = mu(T_B),                O_p=Z_p[i].

Then:

1. **Uniform local inequality:** lambda_B>=delta, for every M and A.
2. **Actual global support:** for each fixed M,B,

       F_B(X) ~ lambda_B kappa X/sqrt(log X).

   In fact all but o_M(X/sqrt(log X)) members of S attain **every** locally
   admissible Gaussian residue modulo M. This exceptional-set statement is
   independent of B.
3. If n_R=|P_R| and D counts distinct positive squared distances, then

       lim_(R->infinity) D(P_R) sqrt(log n_R)/n_R
         = (4 kappa/pi) (lambda_B/delta) >= 4 kappa/pi.

The constant is sharp: ideal-coset masks have lambda_B=delta. The order of
quantifiers is essential: **fix M first, then let X or R tend to infinity**.
No modulus-uniform error, arbitrary finite-set bound, or constant-loss actual
support contraction follows here. See `periodic_norm_support_finite_height.md`.
No Lean files were modified. No claim of historical priority is made.

## 1. The scalar Landau measure

For each p|M define a probability measure mu_p on Z_p. Give 0 mass zero and
specify valuation and conditional unit laws as follows:

| p | valuation law | conditional unit law |
|---|---|---|
| p=1 mod 4 | Pr(v_p=k)=(1-1/p)p^(-k) | uniform on Z_p^* |
| p=3 mod 4 | Pr(v_p=2k)=(1-p^(-2))p^(-2k), odd valuations absent | uniform on Z_p^* |
| p=2 | Pr(v_2=k)=2^(-k-1) | uniform on 1+4Z_2 |

Here “uniform” is normalized multiplicative Haar measure. Put mu=product mu_p.
For split p, mu_p is additive Haar on Z_p, **not** the pushforward of Haar on
O_p: the latter gives valuation k probability
(k+1)(1-1/p)^2 p^(-k).

For inert p, mu_p **is** the norm-pushforward of additive Haar on O_p: write
z=p^k u, and use the surjective norm on unramified units. The same is true at
2: with varpi=1+i, Haar gives v_varpi(z)=k probability 2^(-k-1), N(varpi)=2,
and norms of units are exactly 1+4Z_2, uniformly. These facts also follow from
the norm-filtration calculation in Section 2.

This product mu is the limiting distribution of a uniformly chosen *norm
value* in S intersect [1,X] at the finitely many primes dividing M. Section 4
checks this using the fixed-progression theorem. It is not a distribution
weighted by the number of Gaussian representations.

## 2. Exact local images, including the extra precision at 2

The local conditions are a finite union of scalar congruences; no boundary
regularity assumption or unproved local-to-global principle is needed.
For a Gaussian residue b=a+ci modulo p^e, choose an integral representative.
Within the local norm support N(O_p), its norm image is described as follows.

### Odd p

Put t=min(e,v_p(a),v_p(c)), with valuations of zero capped at e. Then

    N(b+p^e O_p) = {u in N(O_p) : u == N(b) mod p^(e+t)}.           (2.1)

If t=e this is just N(p^e O_p)=p^(2e)N(O_p). Otherwise divide b by p^t.
One coordinate of the resulting primitive vector is a unit. Since 2 is a
unit, varying that coordinate through a p^(e-t)-ball gives every scalar in
N(b/p^t)+p^(e-t)Z_p, by Hensel's lemma. Rescale by p^(2t). This proof applies
to split and inert odd primes alike.

### p=2

Let t=min(2e,v_varpi(b)). If t=2e, the condition is u==0 mod 2^(2e), within
N(O_2). If t<2e, put

    h=2e-t,   k=max(2,floor(h/2)+1).

Then

    N(b+2^e O_2) = {u : u == N(b) mod 2^(t+k)}.                    (2.2)

The values on the right already have valuation t and odd part 1 mod 4.
To prove this, write the ball as b(1+varpi^h O_2) and use

    N(1+varpi^h O_2)=1+2^max(2,floor(h/2)+1) Z_2.                 (2.3)

For h>=3 the 2-adic logarithm and exponential apply, and
Tr(varpi^h O_2)=2^(floor(h/2)+1)Z_2. For h=1, the four global units represent
all cosets of O_2^* modulo 1+varpi^3 O_2 and have norm one. Thus its norm is
1+4Z_2; the h=2 subgroup contains h=3 and has the same norm image. This proves
(2.3), and also the unit-norm assertion in Section 1.

For a global residue b, combine (2.1)--(2.2) at p|M. Consequently T_B, relative
to the product local norm support, is a union of scalar cylinders modulo

    J=M^2 if M is odd,       J=2M^2 if M is even.                 (2.4)

All cylinders for a particular b have the form u==N(b) mod q_(b,p).
Their products and then their union over b must be kept intact: **multiplying
separate marginal densities would generally be wrong**. Formula (2.4) makes
lambda_B an exactly computable rational number.

For example, b=1+2i modulo 4 has norm image 5 mod 8. Merely testing
N(b)==1 mod 4 would incorrectly declare norm 1 locally possible.

## 3. The correlated fiber-gap proof of lambda_B>=delta

Let C be the inverse image of A in product_(p|M) O_p. It has normalized Haar
measure delta. Its difference set is exactly the inverse image of B: if z
reduces to a-a', any lift b of a' gives b and b+z in C.

At split primes choose O_p=Z_p x Z_p, with N(x_p,y_p)=x_p y_p, and write

    product_(p|M) O_p = W x X_split x Y_split,
    L=product_(p|M, p=1 mod 4) p^e.

W is the product of inert and ramified factors. CRT identifies the residue
quotient of Y_split with Z/LZ. For r in Z/LZ, let F_r subset W x X_split be
the fiber of C with Y-residue r; its Haar measure is f_r. A fiber is independent
of the choice of lift of r, because C is a residue cylinder. Thus

    delta=(sum_r f_r)/L.

List the occupied r cyclically. The positive forward gaps g_r sum to L, even
if there is just one occupied residue (then its gap is L). Hence some r has

    f_r/g_r >= (sum f_r)/(sum g_r)=delta.                         (3.1)

Write g=g_r and choose b=(b_W,b_X,b_Y) in the next occupied fiber. For every
(w,x) in F_r, the point (w,x,b_Y-g) belongs to C. Therefore the compact image

    E={(N(w-b_W), -g(x_p-b_(X,p)))_(p split) : (w,x) in F_r}

is contained in N(C-C)=T_B.

The pushforward of **full** Haar measure on W x X_split under this map is

    nu=mu_W x normalized-Haar(product_(p split) g Z_p).

Translations in W do not change its norm-pushforward, and the split factors
are linear scalar maps. Since the preimage of E contains F_r, nu(E)>=f_r.
On the support of nu, the full scalar measure satisfies

    mu(E)=c_g nu(E),    c_g=product_(p split) |g|_p.

Thus

    lambda_B >= mu(E) >= c_g f_r >= f_r/g >= delta,               (3.2)

because product_(p split) p^v_p(g) divides the positive integer g. This uses
no independence assertion about the coordinates **inside F_r**.

If there are no split factors take L=g=1, with a single Y-fiber; this is just
the norm-pushforward comparison on W. For M=1 all products are singletons and
lambda_B=delta=1. Measurability is harmless: all fibers and images used are
compact.

## 4. Counting the locally admissible scalar population

Define

    C_B(X)=#{m in S : m<=X, (m)_p lies in T_B}.

The classical reduced-progression law is: if gcd(a,q)=1 and
 a==1 mod gcd(4,q), then

    #{m in S : m<=X, m==a mod q}
       ~ [(4,q)/((2,q)q)] product_(p|q, p=3 mod 4)(1+1/p)
          kappa X/sqrt(log X).                                 (4.1)

Other reduced residues incompatible with 1 mod 4 have no members of S.
The constant in (4.1) is exactly the product of the probabilities in Section 1
for a unit residue modulo each p^v_p(q).

For completeness, nonreduced residues need no extra distribution theorem.
For a residue a modulo product p^h, if a is nonzero mod p^h, factor out its
fixed valuation v<h (reject odd v at inert primes). If a is zero mod p^h,
factor out p^h at split primes and at 2, and p^(2 ceil(h/2)) at inert primes,
and remove that prime from the remaining progression modulus. The remaining
integer is in S in one reduced progression. All factored odd prime powers
are 1 mod 4, so the 2-adic norm condition transforms correctly. Applying (4.1)
at the rescaled bound gives the product local mass for every scalar cylinder.

By the finite-cylinder description (2.4), summing disjoint residue classes
now proves

    C_B(X) ~ lambda_B kappa X/sqrt(log X).                        (4.2)

The inequality F_B<=C_B alone is not enough. The next section proves that
the missing admissible norms have relative density zero within S.

## 5. Global saturation: a full orientation-switching argument

### 5.1 The exact group of available unit corrections

Let

    G=(O/(M))^*,   U=image of {1,-1,i,-i},   R=G/U,
    d:R->R,       d(c)=c/conjugate(c),       H=d(R).

Since O has class number one, R is its ray class group modulo the rational
ideal (M). Conjugation preserves this modulus, so d is well defined.

**Local norm-one lemma.** The reductions of exact local norm-one units in
product_(p|M) O_p^* are precisely U times {g/conjugate(g):g in G}.
In particular their images in R are exactly H.

Proof: Hilbert 90 gives t=a/conjugate(a) for a norm-one element. For odd inert
p, remove a rational power of p to make a a unit. At a split prime write
t=(u,u^(-1)) and take a=(u,1). At 2 write a=varpi^k v with v a unit. Since
varpi/conjugate(varpi)=i, one has t=i^k v/conjugate(v). Use this **single global
unit** i^k to correct the 2-component; at every odd component the remaining
norm-one unit still has a unit Hilbert-90 representative. Reduction proves
one inclusion, and lifting a unit residue proves the other. Alternatively,
Hilbert 90 here is elementary: a=1+t works when t!=-1, and a=i works for -1.
This argument avoids the false replacement of exact local norm-one units by
the kernel of the finite norm map at a ramified prime. QED.

### 5.2 Almost every sum of two squares has the required switch factors

Choose generators c_1,...,c_s of the finite group R. Set h_j=d(c_j), let o_j
be its order, and put T=sum_j(o_j-1). Ignore generators with o_j=1.
For each j let Q_j be the rational split primes q not dividing M for which
one of the Gaussian prime ideals above q is in ray class c_j.

The prime-ideal theorem in each **fixed** ray class gives

    #{prime ideals in c_j of norm<=Y} ~ Li(Y)/|R|.

Degree-two prime ideals contribute only O(sqrt(Y)); a rational split prime
has two prime ideals above it. Thus each Q_j has a divergent sum of 1/q.
No angular prime theorem, GRH, or modulus-uniform prime theorem is needed.

Here is a sufficient probabilistic fact, using uniform measure on S, not on
representations. For any finite set of rational split primes and any subset
with product d,

    #{m in S, m<=X, d|m}=S(X/d),

so its ratio to S(X) tends to 1/d. Inclusion-exclusion gives asymptotically
independent divisibility indicators with probabilities 1/q. On larger finite
subsets of Q_j the sum of these probabilities diverges, and the probability
of fewer than T successes tends to zero (e.g. by Chebyshev). First fix that
finite subset and let X grow, then enlarge the subset. A finite union over j
shows that all but o_M(S(X)) integers in S have at least T distinct prime
factors in each Q_j. This is a sequential limit, not a uniform sieve estimate.

Such an integer has disjoint selections of o_j-1 primes for each j: greedily
allocate them, since fewer than T primes have previously been used. Pick a
Gaussian generator pi_q in ray class c_j for every selected prime. Starting
with conjugate(pi_q) in a representation, switching that factor to pi_q
multiplies its class in R by h_j. Choosing 0,...,o_j-1 switches for every j
realizes all of H. Higher exponents in m cause no problem: reserve one factor
from each distinct selected prime and leave the other factors fixed.

### 5.3 Nonunit residues are included

Take a switch-rich m in S and any locally admissible b modulo M. Choose local
z_p congruent to b with N(z_p)=m. At primes dividing M, record their valuations:

- at inert p, v_p(m)=2k and v_p(z_p)=k;
- at 2, v_varpi(z_2)=v_2(m);
- at split p, the two valuations of z_p sum to v_p(m).

Choose a global Gaussian integer beta using only primes above p|M with
exactly these valuations. It satisfies

    N(beta)=product_(p|M) p^v_p(m),
    m_0=m/N(beta) in S,       gcd(m_0,M)=1.

Now t_p=z_p/beta is a local unit of norm m_0. Construct a global z_0 of norm
m_0 with the selected switch factors initially conjugated as in 5.2. Every
ratio t_p/z_0 is an exact local norm-one unit. By 5.1 its residue class in R
belongs to H. Switch the reserved factors to match this class, then multiply
by a global unit to match it in G itself. The resulting z_0' has norm m_0
and z_0'==t_p mod M at every p|M. Hence

    z=beta z_0' has N(z)=m and z==b mod M.

There was no bound or truncation on v_p(m). The same richness condition works
for every locally admissible b, with a potentially different representation.
Thus

    0 <= C_B(X)-F_B(X) <= o_M(S(X)).                              (5.1)

Together with (4.2), this proves the claimed actual-support asymptotic.

**Useful exact special case.** If H is trivial, no switches are needed and
local admissibility is sufficient for every m in S, at every height. This
applies to M=1,2,3,4,5. For odd 3 and 5 the norm-one residue group consists
of the four global units; modulo 4 the exact norm-one reductions are again
just those units. It does not extend to arbitrary M (or to products of these
moduli without a new check).

## 6. From actual norms to actual distances in a periodic disk

A difference of P_R belongs to B mod M and has length at most 2R, so
D(P_R)<=F_B(4R^2). Conversely take any vector v reducing to B. Choose residues
a,a' in A with a-a'==v. A point of a'+MO is within M/sqrt(2) of -v/2, by the
covering radius of the square lattice. If

    |v| <= 2R-sqrt(2)M,

that point and its translate by v both belong to P_R. Thus, for R>=M/sqrt(2),

    F_B((2R-sqrt(2)M)^2) <= D(P_R) <= F_B(4R^2).                 (6.1)

This is an actual endpoint construction, not an angular equidistribution
claim. Also

    n_R=delta pi R^2+O_(M,A)(R+1).

For fixed M, (5.1) and (6.1) give the limit in the theorem. Independently of
any analytic estimate, the number of integers in the boundary interval shows

    0 <= F_B(4R^2)-D(P_R) <= 4 sqrt(2)MR+1                       (6.2)

when the lower radius is nonnegative. The endpoint error and the global
saturation error are distinct and must not be conflated.

If I divides the ideal (M), a coset of I gives delta=1/N(I). Its local
difference ideal has norm image of mu-measure 1/N(I): at split primes it is
p^(a+b)Z_p, at inert primes it is p^(2a)N(O_p), and at 2 it is 2^a N(O_2).
Thus lambda_B=delta, proving sharpness.

## 7. Exact checks and sources

`verify_periodic_norm_support_audit.py` uses only integer arithmetic and
`fractions.Fraction`. Its full output is in
`periodic_norm_support_verification.txt`. Checks include:

- all nonempty masks modulo M=1,2,3,4: respectively 1,15,511,65535 cases;
- 30,550 sparse/dense masks modulo 5 and 680 seeded correlated masks at
  prime powers and mixed moduli, including two split primes at M=65;
- exact norm-image enumeration for 1,042 Gaussian residue classes, including
  the extra 2-adic precision, and the local Hilbert-90/unit identity;
- all Gaussian residues for every positive norm up to 5,000 at M=1,...,5;
- a genuine mod-13 local/global failure and a successful finite switch packet:
  2105=5*421, with generators 2+i and 15+14i in the same ray class, attains
  all 12 locally admissible unit residues modulo 13;
- actual periodic-disk endpoint inclusions and the finite-height lemmas in
  the companion note.

These calculations check finite statements; they do not infer any asymptotic.
The complete arguments above supply the asymptotics.

Analytic inputs inspected in the local source corpus:

1. `/corpus/src/2111.12662/sosbias.tex`, lines 12--17: Landau's law and
   Prachar's reduced-progression law, including its constant and necessary
   1 mod gcd(4,q) condition. Its nearby line 11 contains an obvious parity
   typo about inert prime exponents; the proof here uses the correct rule,
   namely that odd inert exponents are forbidden. Only the unconditional
   classical review is used, not the paper's later conditional bias theorem.
2. `/corpus/src/1610.08410/1610.08410.tex`, lines 53--80, especially 63--69:
   prime ideals in a fixed ray class. Only the fixed-modulus asymptotic is
   used. No modulus-uniform meaning is assigned to its displayed error-term
   notation.

Neither reference alone states the saturation conclusion needed here.
Sections 5.1--5.3 are the missing reduction and orientation-switching proof.
