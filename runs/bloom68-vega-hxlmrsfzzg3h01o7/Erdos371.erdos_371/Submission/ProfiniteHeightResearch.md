# Profinite heights of affine annulus laws

## Scope

The height transitions below were proposed by the main assistant and independently
checked by a research agent. They prove new restrictions on the abstract
IS + ANN + USI-AP package in `AffineAnnulusResearch.md`; they do **not** prove
that every such law has zero current, and are not a proof or disproof of the
LPF density statement. No admitted target is used. These are mathematical
arguments, not Lean formalizations.

The main conclusions are:

1. Every integer-ergodic component has, at each prime, an integer-valued height
   (with two infinite endpoints) which increases by the prime valuation of
   the dilation.
2. Full-measure annulus positivity forces this height to be an infinite
   endpoint almost surely, simultaneously at all primes.
3. The part with a summable reciprocal set of bad primes has independent
   rational-coordinate pairs, even if its bad set is infinite and varies
   between components.
4. Possible nonzero current remains only in the nonatomic component part
   whose bad-prime reciprocal sum diverges. This part is NOT shown to vanish.

## 1. Operators and component distributions

On Ω=[0,1]^Q use

```
(A_s z)_q = z_(q+s),  (D_a z)_q = z_(a q),
G_(k,r)=A_r D_(1/k),
R_k ν=(1/k) sum_(0<=r<k) (G_(k,r))_*ν.
```

IS is invariance under T=A_1. ANN is positivity of lR_lν-kR_kν for all
integers l>k>=1. Let E be the standard Borel space of T-ergodic invariant
probabilities, and let ρ be the ergodic-component distribution of ν.
Write F_kθ=R_kθ and ρ_k=(F_k)_*ρ.

As checked in `AffinePairRigidityResearch.md`, §3, R_k preserves ergodicity,
F_kF_m=F_(km), and

```
lρ_l-kρ_k >= 0,
d_TV(ρ_(k+1),ρ_k) <= 1/(k+1).                            (1)
```

Here d_TV is sup over measurable events, half the total variation norm.
These statements follow by uniqueness of the ergodic decomposition of the
positive invariant measure lR_lν-kR_kν. They are NOT annuli for individual
components.

The exact finite-fibre identity is

```
F_kθ=F_kθ' iff θ'=(A_(r/k))_*θ for some 0<=r<k.          (2)
```

Indeed (D_k)_*R_k=P_k=(1/k)sum_(r<k)(A_(r/k))_*, and the summands of
P_kθ are ergodic. Equality of the two finite mixtures supplies (2).
The converse uses R_k(A_s)_*=(A_(ks))_*R_k.

## 2. Heights and the preserving-root obstruction

For θ in E and a prime p, let

* s_p(θ)=sup{j>=0 : (A_(1/p^j))_*θ=θ};
* h_p(θ)=sup{j>=0 : (Ω,θ,T) has an eigenvalue of order p^j}.

Both take values in the nonnegative integers with infinity adjoined. If an
eigenvalue of order p^j occurs, a power of its eigenfunction supplies every
lower p-power order, so these are heights rather than arbitrary sets.

They are Borel. For s_p, each condition is equality of two probabilities
under a continuous coordinate reindexing. For h_p, fix a countable dense
family of continuous cylinder functions in C(Ω). The existence of the
specified eigenvalue is equivalent to a nonzero spectral projection of
one of these functions. The projection's squared norm is the limit of the
squared norms of twisted Cesaro averages, whose integrals are Borel in θ.
The mean ergodic theorem supplies the limit. Taking a countable union over
tests proves measurability.

**Root lemma.** If T is ergodic and a preserving transformation S satisfies
S^p=T, then T has no eigenvalue of order p.

For if f∘T=ζf with ζ of order p, normalize |f|=1. Ergodicity makes f^p a
nonzero constant and the ζ-eigenspace one-dimensional. Since S commutes
with T, f∘S=ηf. The constant pth power gives η^p=1, whereas S^p=T gives
η^p=ζ, a contradiction. Consequently

```
s_p>0 implies h_p=0;  h_p>0 implies s_p=0.              (3)
```

Define e_p with values in Z union {-infinity,+infinity} by

```
e_p = h_p if h_p>0,
e_p = -s_p if s_p>0,
e_p = 0 if both heights are zero.
```

The two possibilities of infinity have their indicated different signs.

## 3. Spectrum on components of powers

For an ergodic invertible probability-preserving T, an ergodic component C
of T^m, and any prime p,

```
h_p(T^m on C) = max(h_p(T)-v_p(m),0),                   (4)
```

with infinity minus a finite integer interpreted as infinity.

It suffices to prove a prime step m=q. The invariant functions of T^q are
the sum of the T-eigenspaces at qth roots of unity. Ergodicity makes each
such eigenspace one-dimensional. If an order-q eigenvalue exists, all q
occur and the T^q-invariant algebra has q atoms of equal mass, permuted
cyclically by T. If no such eigenvalue exists, T^q is ergodic.

In the q-component case, V=T^q on one component has the tower spectrum

```
ζ is a T-eigenvalue iff ζ^q is a V-eigenvalue.
```

Restriction proves one direction. For the converse, propagate a V
eigenfunction g around the q levels by f(T^r x)=ζ^r g(x); the wraparound
is exactly its V eigenrelation. This lowers the q-height by one and
preserves every other prime height.

In the one-component case, T is a preserving qth root of the ergodic T^q,
so the root lemma gives h_q(T^q)=0. For p!=q, an order-p^j eigenfunction
g of T^q is also an eigenfunction of T by one-dimensionality of that
T^q-eigenspace. If its T-eigenvalue is η, then η^q=ζ and η^(p^j)=1
(the latter follows because g^(p^j) is constant). Its order is precisely
p^j. The converse is immediate. This proves (4), including the case of
infinite heights by checking every finite order.

It is not correct in the one-component case to assume that *every* qth
root of an eigenvalue occurs; that assertion was used only for a genuine
q-level tower.

## 4. Exact height transitions

We claim

```
e_p(F_kθ) = e_p(θ)+v_p(k),                             (5)
```

where both infinite endpoints are fixed under addition.

For k=p, put λ_0=(D_(1/p))_*θ and λ=R_pθ. The law λ_0 is T^p-ergodic,
conjugate to (θ,T). Its integer translates form all the T^p-components of
λ. There is one component if s_p(θ)>=1, and p distinct components if
s_p(θ)=0: equality of two branches is invariance of θ under a nonzero
multiple of 1/p, equivalent to invariance under 1/p.

* If s_p>=1, λ=(D_(1/p))_*θ is itself T^p-ergodic, so h_p(λ)=0. Direct
  conjugation of translations gives s_p(λ)=s_p(θ)-1, with infinity fixed.
* If s_p=0, λ has a genuine p-cycle of T^p-components. Formula (4),
  together with the order-p eigenvalue, gives h_p(λ)=h_p(θ)+1. Its
  translation height is zero by (3).

Thus (5) holds at p, including -1 to 0 and 0 to 1.

For a different prime q, θ is conjugate to a T^q-component of F_qθ, so
(4) gives h_p(F_qθ)=h_p(θ). Also, for every j,

```
(A_(1/p^j))_*F_qθ=F_qθ iff (A_(1/p^j))_*θ=θ.           (6)
```

For the forward direction, covariance and (2) show
A_(1/(q p^j))θ=A_(r/q)θ for some r. Multiplying their invariant offset
by q yields invariance under (1-rp^j)/p^j, which is invariance under
1/p^j modulo an integer. Conversely, Bezout writes
1/(q p^j)=u/p^j+v/q. If θ is invariant under 1/p^j, its translate by
1/(q p^j) is a v/q translate, erased by R_q. This proves (6).
Both heights are therefore preserved at coprime prime steps. Factoring k
and using commutation proves (5).

## 5. ANN forces only the infinite endpoints

Fix p and let β be the distribution of e_p under ρ. At k=p^j, (5) gives
the distribution β+j, with infinite endpoints fixed. At l=p^j+1, all
prime factors are different from p, so the distribution is β. Pushing (1)
through the Borel height map gives

```
d_TV(β+j,β) <= 1/(p^j+1).                              (7)
```

For every finite interval [-M,M] in Z, its β+j mass is
β([-M-j,M-j]), which tends to zero by finiteness of β. Equation (7)
therefore implies β([-M,M])=0. Taking the union over M proves β(Z)=0.
There are countably many primes, hence

```
e_p(θ) in {-infinity,+infinity} for every p,
for ρ-almost every θ.                                  (8)
```

No SI, continuity of a real action, or componentwise ANN has entered.
Define the Borel bad-prime set

```
S(θ)={p : e_p(θ)=+infinity}.
```

On the full-measure set in (8), every F_k preserves S exactly. A component
has all p-power rational eigenvalues and no p-power translation invariance
when p is bad; it has all p-power translation invariances and no rational
p-spectrum when p is good.

### Invariant restrictions and the SI quantifiers

For any Borel collection of bad-prime sets, its inverse image B in E is
F_k-invariant. The sublaw ν_B=∫_B θ dρ therefore satisfies ANN by restricting
the positive component inequalities. If its mass is α>0, the normalized
sublaw κ=ν_B/α inherits USI with a factor 1/α in mean square, since
R_kν_B<=R_kν. This is a restriction to a **positive-mass invariant set of
components**, not passage of ANN or a uniform estimate to each component.

Integer coordinate marginals of κ are F by stationarity, Jensen, and SI
for every centered continuous test. Rational-coordinate SI and marginals
follow using the valid branch inequality

```
(G_(d,0))_*R_kκ <= d R_(dk)κ.
```

For q=b/d and integer step h, its use on the integer AP b+dhj bounds

```
E_(R_kκ) |L^-1 sum_(j<=L) ψ(Z_(q+hj))|²
 <= d e_(L,dh)(ψ)²,                                    (9)
```

where e includes the restriction's normalization factor. This is uniform
in k for each fixed d,h. It neither makes one branch stationary nor
asserts SI for coordinate products. Jensen now supplies all rational
marginals F for κ.

## 6. Summable bad primes imply pair independence

### 6.1 Integrable reciprocal mass

Let κ be a normalized restricted law as above, with component distribution
β, and suppose

```
a_p=β{θ:p in S(θ)},   sum_p a_p/p < infinity.            (10)
```

If m has no prime factor in S(θ), Bezout and the good-prime infinite
translation heights imply P_mθ=θ. Convexity and a union bound give

```
δ_m=d_TV(P_mκ,κ) <= sum_(p|m) a_p.                     (11)
```

Fix distinct rational coordinates b/d<c/d, bounded φ, and bounded
F-centered ψ. Let C=E_κ φ(Z_(b/d))ψ(Z_(c/d)), and
B=||φ||_infinity ||ψ||_infinity. Fix Y and choose M divisible by d and by
every prime <=Y. For K=1 mod M put m_r=K+Mr, 1<=r<=L.

Use D_mR_m=P_m, then shift the two coordinates by the integer
-(m-1)b/d. The first becomes b/d and the second becomes
c/d+(m-1)(c-b)/d. Comparing R_(m_r) with R_K by ANN, and using (9) for
the second-coordinate AP, gives

```
|C| <= ||φ|| sqrt(d) e_(L,M(c-b))(ψ)
       + (2B/L) sum_(r<=L) δ_(K+Mr)
       + B M(L+1)/K.                                  (12)
```

The rational origin and AP step are fixed before letting K grow. The
initial integer displacement of the AP is removed by IS inside its
mean-square norm. No growing-step uniformity is asserted.

Average K=1 mod M over [X,2X], a set of N_X~X/M integers. No m_r has a
prime factor dividing M. For p not dividing M, the divisibility
p|K+Mr selects at most N_X/p+1 such K. Thus

```
E_K [L^-1 sum_(r<=L) δ_(K+Mr)]
 <= sum_(p>Y) a_p/p + N_X^-1 sum_(p<=2X+ML) a_p.        (13)
```

The last term is o(1), for fixed M,L. Indeed (10), split at any fixed
cutoff, implies sum_(p<=x)a_p=o(x): each tail a_p is at most x(a_p/p),
and the tail reciprocal sum is arbitrarily small. This argument needs
no prime number theorem.

Choose arbitrarily large K attaining at most the average in (13). In
(12) let K tend to infinity, then L tend to infinity with M fixed, then
Y tend to infinity. The result is C=0. Centered product tests and the
common marginals prove independence of every distinct rational pair.

### 6.2 Finite reciprocal mass almost surely

Put H(θ)=sum_(p in S(θ))1/p. This is Borel and F_k-invariant. Restrict to
{H<=N}; any positive normalized restriction satisfies (10) since its
expected H is at most N. Its rational pair laws are therefore product.
Let N grow. The sublaw ν_fin on {H<infinity}, of mass α, satisfies

```
Law_(ν_fin)(Z_q,Z_q') = α(F tensor F), q!=q'.            (14)
```

Together with the atomic-part theorem in `AffinePairRigidityResearch.md`,
this gives, for atomless F and J(ν)=E_ν sgn(Z_1-Z_0),

```
|J(ν)| <= ρ_nonatomic {θ : H(θ)=infinity}.               (15)
```

The right side is NOT proved zero. A possible nonzero-current law may be
restricted and normalized to precisely that invariant nonatomic part.

## 7. Why the remaining spectral shortcut fails

There are fields with all p-heights +infinity, strong coordinate SI, and
nonzero current, but which fail ANN. For completeness, take independent
U Haar on Zhat, a stationary circle reset chain X_n with transition
one-half rotation by 1/3 and one-half independent Haar reset, and independent
bilateral Haar streams W_(m,n), m>=2. Choose disjoint nonzero rational
cosets r_m,s_m modulo Z, and put, modulo one,

```
Z_n=X_n,
Z_(n+r_m)=W_(m,n),
Z_(n+s_m)=W_(m,n)+((U+n) mod m)/m.
```

Fill remaining cosets by independent Haar streams. The full integer
system is the product of the ergodic odometer and a mixing stream system,
so it is ergodic. Differences at the paired cosets recover U mod m for
every m; the full field recovers the other streams. Thus it has every
rational p-power eigenvalue, for every p, and by the root lemma its
translation heights are zero.

Every coordinate is uniform even conditional on U. Apart from its one
paired coset partner, each noninteger coordinate is independent of the
others; integer-chain covariance is bounded by 2^(-|n-n'|) Var(ψ).
Summing rows gives mean-square coordinate averages <=3 Var(ψ)/L for any
L distinct rational coordinates. Every branch preserves distinctness,
so this bound holds uniformly over the R_k orbit. Its current is 1/6.

It nevertheless fails ANN. Its integer lag-two current is -1/12, whereas
that of R_2 is 1/12: half is the lag-one current of X, and the noninteger
half-coset stream has independent entries at consecutive integers. Both
full laws are ergodic and different, hence mutually singular. This
contradicts ν<=2R_2ν, which ANN would require.

This near-miss shows that the height dichotomy and conditional coordinate
marginals alone do not prove pair independence. It is NOT a countermodel
to the full package or to the LPF conjecture. The divergent-bad-prime,
nonatomic case with actual ANN is still unresolved.
