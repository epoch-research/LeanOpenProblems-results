# Erdős 371: rough odd-character moments — verified partial estimates

## Status

**This does not prove that the natural density is 1/2.** It proves further removable ranges in the supplied Alladi reduction, including a treatment of the modulus-dependent smoothness cutoff. The remaining long-modulus signed first moment is not estimated by o(X).

No Lean file was edited. In particular, `Submission/Spec.lean` remains unchanged. The SHA-256 checked at the start was

```
d48bb112dcd4fd5c98dae80077b7384df62a14ef9a919fe7d476b9c5ace427bb
```

The main deductions in this note are:

1. An exact regrouping by primitive conductor, and an absolute bound showing that any polylogarithmic-sized family of exceptional primitive characters is harmless.
2. A maximal-cutoff transfer lemma: a **fixed-cutoff** mean progression estimate can be upgraded to a supremum over smoothness cutoffs by positivity and a finite quantile grid. No uniformity in a modulus-dependent cutoff is assumed.
3. For Y = exp(log X/(3 log log X)), any epsilon > 0 and 0 < b < 1/2,

   ```
   sum_{d <= X^(17/33-epsilon), P^-(d)>Y} |mu(d)|
       |Psi_{<P^-(d)}(X;d,1)-Psi_{<P^-(d)}(X;d,-1)|
       <<_{epsilon,b} X/(log X)^b.                         (A)
   ```

   This is a deduction from the **proof** of Fouvry–Radziwiłł's dispersion result, retaining the modulus-dependent exceptional-set bound. Merely summing their stated weak dyadic corollary would not prove (A).
4. For every epsilon > 0 there is c = c(epsilon) > 0 such that

   ```
   sum_{d <= X^(3/5-epsilon), Y<P^-(d)<=X^c} |mu(d)|
       |Psi_{<P^-(d)}(X;d,1)-Psi_{<P^-(d)}(X;d,-1)|
       <<_epsilon X Y^(-1/4) (log X)^5 sqrt(log log X).    (B)
   ```

   Here roughness removes the low-conductor terms in a checked theorem of Drappeau–Granville–Shao exactly. The estimate is stronger than any fixed logarithmic saving.

These are deductions from established dispersion theorems, not claims of a new dispersion theorem or a literature-priority claim.

## 1. Definitions and the exact endpoint audit

Let X >= 3 be an integer, P(1)=1, and P^-(1)=infinity. Put

```
s_n = sgn(P(n+1)-P(n)),
J(X) = sum_{1<=n<X} s_n,
J_y(X) = sum_{1<=n<X} s_n 1_{max(P(n),P(n+1))>y}.
```

Consecutive largest prime factors do not tie: a common prime would divide 1. Thus J(X)=2 A(X)-(X-1), where A(X) counts ascents on this interval. Consequently J(X)=o(X) is exactly the desired natural-density assertion, up to the harmless initial endpoint.

For a prime p define

```
Psi_{<p}(T;d,a) = #{1<=m<=T : P(m)<p, m=a mod d},
Delta_p(X;d) = Psi_{<p}(X;d,1)-Psi_{<p}(X;d,-1),
B_d(X) = Psi_{<P^-(d)}(X;d,1)-1
         -Psi_{<P^-(d)}(X-1;d,-1).
```

The finite Alladi identity is

```
sum_{d|a, d>1, P^-(d)>y} mu(d) 1_{P(b)<P^-(d)}
    = -1_{P(a)>max(y,P(b))}.                              (1)
```

Proof: list the distinct prime factors of a increasingly. The sum of mu(d) over divisors having a specified least prime p is
`- product_{ell|a, ell>p}(1-1)`. Only p=P(a) survives. This proof also covers a=1 by an empty sum.

Apply (1) to both orientations of each adjacent pair. It gives the **exact** formula

```
J_y(X) = sum_{2<=d<=X, P^-(d)>y} mu(d) B_d(X).             (2)
```

The `-1` in B_d is important: the raw progression count at residue 1 contains m=1, whereas the corresponding shifted pair does not.

If

```
T(X;U,y) = sum_{2<=d<=U, P^-(d)>y} mu(d) Delta_{P^-(d)}(X;d),
M_y(X) = sum_{2<=d<=X, P^-(d)>y} mu(d),
E_y(X) = sum_{d|X+1, 2<=d<=X, P^-(d)>y}
              mu(d) 1_{P(X)<P^-(d)},
```

then (2) says exactly

```
J_y(X) = T(X;X,y)-M_y(X)+E_y(X),     |E_y(X)|<=2.          (3)
```

The last bound follows by adding back the possible divisor d=X+1 and applying (1). Also
`|J(X)-J_y(X)| <= Psi(X,y)`.

### Recovering the supplied truncation

Write L=log X, ell=log L, Y=exp(L/(3 ell)), and U=floor(X/L^A) for fixed A>0. The standard upper-bound sieve gives

```
#{d<=t : P^-(d)>Y} << t/log Y             (t>=Y^2).
```

It follows by partial summation that

```
sum_{U<d<=X, P^-(d)>Y} (X/d+1)
    << X(1+log(X/U))/log Y
    <<_A X ell^2/L.                                      (4)
```

This bounds the discarded raw progression counts absolutely. It also bounds the m=1 endpoint in (3), since `|M_Y(X)| << X/log Y`.

No delicate uniform smooth-number asymptotic is needed for the omitted Y-smooth pairs. Rankin's argument with alpha=1-1/log Y gives

```
Psi(X,Y) <= X^alpha product_{p<=Y}(1-p^(-alpha))^(-1)
          << X exp(-L/log Y) log Y
          << X/(L^2 ell).                                (5)
```

Indeed, `exp(t)-1 <= (e-1)t` for 0<=t<=1 and
`sum_{p<=Y} log p/p << log Y` show that the Euler product in (5) is `O(log Y)`.

Hence the user's formula, with the indicated signed orientation, is recovered:

```
J(X) = T(X;U,Y) + O_A(X ell^2/L).                         (6)
```

## 2. Exact primitive-conductor regrouping

On `P(m)<P^-(d)` we automatically have `(m,d)=1`. Orthogonality therefore gives

```
Delta_{P^-(d)}(X;d)
  = 2/phi(d) sum_{chi mod d, chi(-1)=-1}
                  sum_{m<=X, P(m)<P^-(d)} chi(m).         (7)
```

Since mu(d) vanishes off squarefree d and Y>2, all contributing d are odd and squarefree. Every character modulo d is induced from one primitive character of conductor q|d. If that character is odd, q>1, so

```
q >= P^-(d)>Y.                                           (8)
```

There are **no** low-conductor nonprincipal characters hidden in this family.

For Z>=1, t>=Y and q squarefree define the finite weight

```
W(Z,t;q) = sum_{r<=Z, (r,q)=1, P^-(r)>t} mu(r)/phi(r),     (9)
```

including r=1. Regrouping (7) by conductor and then interchanging r and m gives the exact identity

```
T(X;U,Y)
 = 2 sum_{2<=q<=U, mu(q)^2=1, P^-(q)>Y} mu(q)/phi(q)
       sum_{psi primitive mod q, psi(-1)=-1}
       sum_{m<=X, P(m)<P^-(q)} psi(m)
          W(U/q, max(Y,P(m));q).                         (10)
```

To check it, set d=qr with `(q,r)=1`. On the smooth support an induced character agrees with psi; there is no extra coprimality correction. The original condition is exactly
`P(m)<min(P^-(q),P^-(r))`, which produces (9).

**No Dickman approximation to W is used.** Such an approximation inside (10) would itself need a separately justified aggregate error estimate.

### Exceptional characters are absolutely harmless if they are few

Let D be any set of squarefree Y-rough moduli <=X, and set

```
H(D) = sum_{d in D} 1/phi(d).
```

Euler products and Mertens' theorem give

```
H(D) <= product_{Y<p<=X}(1+1/(p-1))
     = product_{Y<p<=X}(1-1/p)^(-1)
     << L/log Y << ell.                                 (11)
```

The same bound applies to the absolute r-sum in (9), with 1 added when its range lies below Y. Also `phi(q)>=q/2` for all squarefree Y-rough q<=X, once X is large: the logarithm of q/phi(q) is at most `2 L/(Y log Y)`.

Consequently the total contribution to (10) from any specified family E of primitive characters is at most

```
<< X (L/log Y) sum_{psi in E, cond(psi) Y-rough} 1/cond(psi)
<< X ell |E|/Y.                                         (12)
```

For `|E|<=(log X)^B`, this is smaller than `X/(log X)^C` for every fixed C, eventually. This statement does not assert that all characters requiring attention form such a small family. It shows that an isolated potential Siegel character, or a polylogarithmic exceptional family, is not the remaining obstruction.

## 3. A maximal-cutoff transfer lemma

This is the step that prevents an unjustified use of uniformity in the moving smoothness cutoff.

Use closed cutoffs temporarily:

```
A_d(z;a) = #{m<=X : P(m)<=z, m=a mod d},
F_d(z) = #{m<=X : P(m)<=z, (m,d)=1},
E_d(z;a) = A_d(z;a)-F_d(z)/phi(d),
F(z) = Psi(X,z).
```

Fix a finite family D of moduli, a residue a coprime to them, and an interval `[Z0,Z1]` with Z0>=2. Suppose that, **for every fixed z in this interval with the same constant**, a known estimate gives

```
sum_{d in D} |E_d(z;a)| <= B.                            (13)
```

Let `H=sum_{d in D}1/phi(d)`. Then for every 0<eta<=1,

```
sum_{d in D} sup_{Z0<=z<=Z1}|E_d(z;a)|
 <= (eta^(-1)+2) B + (eta X+X/Z0) H.                     (14)
```

Thus, whenever B<=XH,

```
sum_{d in D} sup_z |E_d(z;a)|
    << B + sqrt(B X H) + XH/Z0.                         (15)
```

Proof: each jump of F at a prime p>=Z0 is at most X/p<=X/Z0. Starting at Z0, choose the first new prime at which F has increased by at least eta X, and repeat, finally including Z1. There are at most eta^(-1)+2 grid points, and on each cell `[z_j,z_(j+1)]` the increase of F is at most `eta X+X/Z0`. Both A_d and F_d are increasing. Hence, throughout the cell,

```
|E_d(z;a)| <= max(|E_d(z_j;a)|,|E_d(z_(j+1);a)|)
             +(F(z_(j+1))-F(z_j))/phi(d).
```

Sum over d and bound the maximum over grid points by their sum, using (13) at the finite grid. This proves (14); optimize eta for (15).

The grid is allowed to depend on X. Its validity follows from a fixed-cutoff estimate uniform in z, whose hypotheses must be checked separately. No interchange of an unproved supremum with a mean estimate occurs. Left limits give the identical conclusion for strict cutoffs, including z=P^-(d).

## 4. Small-cutoff cancellation to exponent 3/5

### Precisely checked input

Drappeau, Granville and Shao, *Smooth-supported multiplicative functions in arithmetic progressions beyond the x^(1/2)-barrier*, arXiv:1704.04831, Mathematika 63 (2017), 895–918.

The source file is `/corpus/src/1704.04831/1704.04831.tex`.

- Lines 155–174 define

  ```
  u_R(n;d)=1_{n=1 mod d}
           -1/phi(d) sum_{chi mod d, cond(chi)<=R} chi(n).
  ```

- The theorem labelled `thm:equidist-noMT`, lines 178–185, says: for each fixed epsilon>0 there are C,c0>0 such that, if

  ```
  1<=R<=X^c0,  (log X)^C<=z<=X^c0,
  ```

  then, uniformly for admissible a1,a2 and f in their class C,

  ```
  sum_{d<=X^(3/5-epsilon), (d,a1 a2)=1}
    |sum_{m<=X,P(m)<=z} f(m) u_R(m inverse(a1) a2;d)|
       <<_epsilon R^(-1/2) X (log X)^10.                 (16)
  ```

Take f=1, a1=+1 or -1, a2=1, and R=Y/2. For every Y-rough d, (8) says the only character in the low-conductor sum is the principal character. Thus the inner expression is **exactly** E_d(z;1) or E_d(z;-1).

Choose c=c0/2 and restrict z to `[Y/2,X^c]`. All hypotheses of (16) hold for sufficiently large X; in particular Y is super-polylogarithmic but X^(o(1)). Consequently (13) holds on the squarefree Y-rough moduli <=X^(3/5-epsilon) with

```
B <<_epsilon X Y^(-1/2) L^10,
H << ell.
```

Apply (15) to both signs. The B term and the jump term are smaller than the square-root term. This proves (B):

```
sum_{d<=X^(3/5-epsilon), Y<P^-(d)<=X^c} |mu(d)|
          |Delta_{P^-(d)}(X;d)|
  <<_epsilon X Y^(-1/4) L^5 sqrt(ell).                   (17)
```

This use of roughness is stronger than merely deleting the principal character by odd parity: it removes **every** low-conductor term in the checked dispersion theorem.

## 5. All cutoffs on rough moduli to exponent 17/33

### Precisely checked inputs

Fouvry and Radziwiłł, *Level of distribution of unbalanced convolutions*, arXiv:1811.08672. Local source: `/corpus/src/1811.08672/FouvryRadzi7.tex`.

- `cor:Main`, lines 66–77, especially part (i), gives arbitrary logarithmic savings for a convolution of two divisor-bounded sequences, one Siegel–Walfisz, on `t<mn<=2t`, averaged over `Q<d<=2Q`, provided its short factor N satisfies

  ```
  exp((log t)^rho) <= N <= Q^(-11/12) t^(17/36-rho).        (18)
  ```

- `le:shiu`, lines 307–314, is the upper bound for nonnegative multiplicative functions in progressions used below.
- Lines 1004–1070 give the small-prime decomposition underlying the multiplicative-function corollary. In particular `le:trivialS` retains an exceptional-set bound proportional to `t/phi(d)`.

It is important **not** simply to sum the stated `cor:mult` bound over O(log X) dyadic modulus blocks; its saving is less than one power of log X. Instead retain the following pointwise exceptional contribution.

### Uniform fixed-cutoff estimate on rough moduli

Let Q=X^(17/33-epsilon), and choose an arbitrarily small fixed sigma>0 with sigma<epsilon/20 and sigma<1/20. For every fixed z, put `g_z(n)=1_{P(n)<=z}`. Its prime restriction is Siegel–Walfisz **uniformly in z**: truncating a prime interval at z introduces at most another endpoint in the ordinary prime Siegel–Walfisz theorem. The additional coprimality condition in the definition of Siegel–Walfisz removes only primes dividing that additional modulus; its permitted divisor-function factor handles them. Thus the dispersion constants can be chosen independently of z.

Here is an explicit version of the decomposition, so the asserted uniformity is checkable. On each `t<n<=2t`, with `t>=X/(log X)^K`, let

```
U_t=exp((log t)^sigma),    V_t=t^sigma.
```

Partition `(U_t,V_t]` into intervals `I_j=(u_j,u_(j+1)]` of relative length comparable to `(log t)^(-B0)`, B0>2 fixed. Call an integer good when it has a prime factor in this interval and its **first occupied prime interval** contains exactly one prime factor, counted with multiplicity. (Requiring every interval to have this property is unnecessary.)

Every good integer has a unique factorization

```
n = b p c,
all prime factors of b <= U_t,
p in the first occupied interval I_j,
all prime factors of c > the upper endpoint of I_j.       (19)
```

This is exactly a convolution of a short prime sequence with an arbitrary 1-bounded cofactor sequence. For g_z the prime coefficient is `1_{p in I_j, p<=z}`; all constants in its Siegel–Walfisz property are uniform in z. The cofactor is restricted by `P(bc)<=z`, which is allowed because that sequence can be arbitrary and 1-bounded.

There are only polynomially many logarithmic prime intervals. Condition (18) holds with rho=sigma/2, uniformly for all dyadic modulus blocks below Q, since eventually

```
Q <= t^(17/33-epsilon/2),
17/36-(11/12)(17/33)=0,
17/36-(11/12)(17/33-epsilon/2)-sigma/2
       = 11 epsilon/24-sigma/2 > sigma.                  (20)
```

The lower bound in (18) also holds because the short primes exceed `exp((log t)^sigma)`. Any fixed power of log t lost in the interval decomposition and dyadic modulus summation is absorbed by choosing the arbitrary saving in `cor:Main` sufficiently large. The good part therefore has error `O_R(X/L^R)` for every prescribed R.

For completeness, the complement has the following bound, uniformly for d<=t^(3/4):

```
#{t<n<=2t : n=a mod d, n bad}
  <<_{sigma,B0} t/phi(d)
        ((log t)^(-1+sigma)+(log t)^(1-B0)).              (21)
```

There are two cases.

1. No prime factor lies in `(U_t,V_t]`. Apply Shiu to its multiplicative indicator. The relevant prime product is `O(log U_t/log V_t)`, namely `O_sigma((log t)^(-1+sigma))`.
2. Two prime factors r,s, including a possible repeated prime, lie in one small interval. The union bound and `(rs,d)=1` reduce the count to progressions of length comparable to `t/(rs)`. Since `rs<=t^(2 sigma)` and d<=t^(3/4), the `+1` in the elementary progression bound is absorbed by `t/(d rs)`. Brun–Titchmarsh in each short prime interval gives `sum_{p in I_j}1/p << (log t)^(-B0)`. Summing squares over `O((log t)^(B0+1))` intervals gives the second term in (21).

This argument is independent of z and bounds the contribution of g_z by positivity. The same bound for the subtracted mean follows by taking d=1 before dividing by phi(d).

Now restrict the moduli to squarefree Y-rough d. Equation (11) makes the sum of (21) at most

```
<< X L^(-1+sigma) ell,
```

after B0 is chosen large enough. The bottom interval `m<=X/L^K` has total discrepancy at most `2(X/L^K)H+Q`, by the elementary progression bound, and is negligible for sufficiently large K. We have proved, uniformly in the fixed cutoff z and separately for a=+1,-1,

```
sum_{d<=Q, mu(d)^2=1, P^-(d)>Y} |E_d(z;a)|
       <<_{epsilon,sigma} X L^(-1+sigma) ell.             (22)
```

Apply (15) on `[Y/2,X]`, with `H<<ell`. The result is

```
sum_{d<=Q, mu(d)^2=1, P^-(d)>Y} sup_z |E_d(z;a)|
       <<_{epsilon,sigma} X ell L^(-(1-sigma)/2).         (23)
```

The negligible grid-jump term is absorbed. Since sigma can be chosen arbitrarily small subject to (20), (23), for both signs and strict cutoffs, proves (A) for every 0<b<1/2.

## 6. What remains, and what parity or reciprocity does not supply

Combine (6), (17), and (A). For fixed small epsilon>0, fixed A>0, and any 0<b<1/2, put

```
Q0=X^(17/33-epsilon), Q1=X^(3/5-epsilon), U=floor(X/L^A).
R_X={d : Q0<d<=U, P^-(d)>Y,
          and [d>Q1 or P^-(d)>X^c]}.
```

Then

```
J(X) = sum_{d in R_X} mu(d) Delta_{P^-(d)}(X;d)
       +O_A(X ell^2/L)+O_{epsilon,b}(X/L^b).              (24)
```

The missing statement is that the **signed sum in (24) is o(X)**. Nothing proved here establishes that statement.

### Functional equations

For primitive odd psi modulo q, the usual completion is

```
Lambda(s,psi)=(q/pi)^((s+1)/2) Gamma((s+1)/2)L(s,psi),
Lambda(s,psi)=tau(psi)/(i sqrt(q)) Lambda(1-s,conj(psi)).
```

Oddness does not make its root number -1. Primitive real odd quadratic characters have root number +1. Conjugate odd characters contribute conjugate sums, not opposite sums.

More importantly, the Dirichlet series for the inner smooth sum is the finite Euler product

```
product_{p<z}(1-psi(p)p^(-s))^(-1).
```

It does not inherit the functional equation of L(s,psi). Writing it as an L-function times a complementary Euler product does not remove that complementary product or its moving cutoff. The functional equation is therefore not an additional cancellation identity for (7) or (10).

Even at a purely local level, the odd projection does not remove the positive diagonal in a dispersion argument. For d>2,

```
1/phi(d) sum_{a in (Z/dZ)^*}
        |1_{a=1}-1_{a=-1}|^2 = 2/phi(d).                (25)
```

The constant mode is removed, but the quadratic mass remains.

### A completely exact prime-block transformation

Let

```
C_X(p,q)=#{1<=n<X : p|n, q|n+1},
R_X(p,q)=C_X(p,q)-C_X(q,p).
```

For any set Pset of primes p>sqrt(X), expansion of the smoothness condition terminates after one large prime. Thus

```
sum_{p in Pset} mu(p) B_p(X)
  = sum_{p in Pset} 1_{p|X}
    +sum_{p in Pset} sum_{q>p, q prime} R_X(p,q).         (26)
```

Proof: for m<=X,
`1_{P(m)<p}=1-sum_{q>=p, q|m}1`.
There cannot be two prime factors >=p. The q=p term vanishes on the neighboring congruence. Finally `R_X(p,1)=-1_{p|X}`. This proves (26), including its endpoint.

The rightmost term counts, with opposite signs, prime solutions to

```
b q-a p=+1      and      b q-a p=-1,
a p<=X, b q<=X, p in Pset, q>p.                          (27)
```

The cofactors satisfy `a<=X/p`, `b<=X/q`. The two signs have identical local factors, but no all-scale cancellation estimate for the required aggregate follows from that equality. In particular mu(p)=-1 throughout this block: there is no outer Möbius oscillation on the prime moduli to exploit.

For p,q>X^(1/2+delta), the two CRT solutions cannot both lie below X once X is large, since their representatives sum to pq-1>2X-1. Thus the remaining antisymmetric terms are genuine isolated signed occurrences, not complete periods with their main terms left uncancelled.

Equation (26) is not a claim that its prime block must separately be o(X) for Erdős 371; cancellation between blocks is logically possible. It identifies a concrete sector left uncontrolled by the methods above. No unproved binary Chowla or prime-pair asymptotic has been assumed.

### Optional exact removal of the smooth cutoff, with a cost

A second exact Alladi identity is

```
s_n 1_{max(P(n),P(n+1))>Y}
 = sum_{q|n(n+1), q>1, P^-(q)>Y} mu(q)
       (1_{P^-(q)|n}-1_{P^-(q)|n+1}).                    (28)
```

This follows by applying the same least-prime/last-prime cancellation to the distinct prime factors of n(n+1), labelled by which adjacent integer they divide. It removes the smoothness cutoff entirely, but introduces moduli as large as X(X-1). Each complete modulus has zero oriented root count by n -> -n-1; the incomplete long-modulus tail remains. It is a transformation, not a bound for that tail.

## 7. Verification and limitations

`Submission/RoughOddMomentVerification.py` performs independent finite checks of:

- the exact Alladi identity (1), the shifted endpoint formula (2), and (3);
- odd-character orthogonality and the primitive-conductor regrouping (10), by explicitly enumerating characters on odd squarefree moduli;
- the monotonicity/grid inequality used in (14);
- the prime-block identity (26) and the oriented quadratic-root identity (28);
- the exact first-occupied-prime-interval factorization (19);
- the critical rational exponent calculation in (20).

These finite checks are not evidence for the asymptotic density and are not substitutes for the proofs. The asymptotic inputs and their parameter ranges are separately specified above.

Network DNS was unavailable. The cited results were checked in the local source corpus; this note makes no claim about research published after that corpus. Teräväinen's logarithmic theorem and Tao–Teräväinen's almost-all-scales theorem are not used to infer an all-scales conclusion here.

### Recorded finite-check outcome

The verification run passed 21,600 pointwise Alladi checks, 1,673 finite endpoint/duality checks, 120 odd-character orthogonality checks, 27 primitive-conductor regroupings, 54 rational quantile-grid checks, 1,194 prime-block checks, 3,594 quadratic-root checks, and 1,797 first-occupied-interval factorization checks. Character evaluations were checked to tolerances 1e-8 and 2e-8; the other identities use integer or rational arithmetic. The exponent margin was checked with exact rational arithmetic. An additional independent trial-division implementation passed 11,790 two-orientation Alladi checks on coprime pairs. The specification SHA-256 remained unchanged after all work.
