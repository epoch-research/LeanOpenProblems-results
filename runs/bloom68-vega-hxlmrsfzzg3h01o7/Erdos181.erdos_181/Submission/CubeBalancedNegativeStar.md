# A balanced relation with divergent negative fifth-star load

## Status and scope

This is **not a proof or disproof of Erdős 181**. It gives a new obstruction to
one proposed sufficient estimate: small one-coordinate-balanced bad probability
does not bound even the **negative part** of the raw centered-polymer root load
uniformly in the cube dimension. The earlier fourth-star example in
`CubeBalancedStarExpansion.md` had positive leading activities and did not show
this. The present fifth-star activities are eventually negative.

The conclusion holds for iid moments and for the corresponding local moments
under uniform injective sampling, on alphabets of size a fixed constant times
`2^(d-1)`. It does not assert an exact polymer factorization for injections,
does not rule out a different resummation, and does not refute the balanced
avoidance assertion. In fact Section 7 gives avoiding injections for this example.
No realization as an original two-colour graph counterexample or as its
edge-fugacity minimizer is asserted.

## 1. An exactly balanced zero-one relation

Fix an integer `K>=16` and a dimension `d>=6`. Set

`q=1/(Kd)`, `u=1-q`, `r=binom(d-1,2)`, `L=(Kd-1)^2`, `w=r/L`.

First consider a weighted symmetric relation `W` on Bernoulli(q) types, with
"rare" denoted by 1. If `J` is the number of rare coordinates, put

* `W=1` for `J>=3`;
* `W=0` for `J=1,2`;
* `W=w` for `J=0`.

Let `p=Pr(Bin(d-1,q)>=2)`. A fixed rare coordinate has conditional mean `p`.
A fixed ordinary coordinate has conditional mean

`Pr(Bin(d-1,q)>=3)+w*u^(d-1)=p`,

because `w*u^(d-1)=binom(d-1,2)*q^2*u^(d-3)` is exactly the missing
binomial probability. Also

`0<p<=binom(d-1,2)*q^2<1/(2K^2)`, and `0<w<1`.

For an actual zero-one relation take

`Omega=[Kd] x (Z/LZ) x [s]`, `N=Kd*L*s`,

where one of the `Kd` types is rare. A tuple is bad if it has at least three
rare types, or if all its types are ordinary and its tag sum modulo `L` lies
in `{0,...,r-1}`. Ignore the copy coordinate. Given any single full label,
the all-ordinary tag sum is still uniform using any one other independent
tag. Thus the bad probability is exactly `p` conditional on **every** full
label. This is a symmetric zero-one relation with exact iid one-coordinate
balance, including the sampling convention that permits repetitions.

For any fixed `C>=1` choose

`s=ceil(C*2^(d-1)/(KdL))`.

Then `C*2^(d-1)<=N<C*2^(d-1)+KdL`. In particular, the construction is available
at a fixed linear host size asymptotically, not only on superexponential alphabets.

## 2. Exact centered expansion on a five-star

Let `E,O` be the even and odd classes of `Q_d`, and let `B_y` be badness on
the `d` even neighbours of an odd centre `y`. Write

`g_y=(1_(B_y)-p)/(1-p)`.

Select five distinct neighbours `y_1,...,y_5` of one even hub `x`. Their shared
variables consist of `x` and one variable `z_ij` for each of the ten pairs of
centres. Each centre has exactly `d-5` private variables. These private blocks
are disjoint. Since `d>=6`, each block has a uniform tag, so private integration
turns the zero-one relation into the weighted calculation **exactly**, even
after all shared full labels have been fixed.

Conditional on a rare hub, the normalized conditional row function has the
centered Bernoulli expansion

`sum_(nonempty J subset incident pairs) a_|J| product_(e in J)(Z_e-q)`.

The constant coefficient is zero by balance. Put `t=(d-2)q`. Since

`1-p=u^(d-2)*(1+t)`,

the coefficients for `1<=j<=4` are exactly

`a_j=(-1)^j*(j-1-t)/(u^j*(1+t))`.

For example, the first coefficient is the normalized probability of exactly
one rare among `d-2` fresh coordinates, and the second is the normalized
probability of zero minus that of one among `d-3` coordinates. In particular

`a_1=t/[u(1+t)]`, `a_2=(1-t)/[u^2(1+t)]`.

Let `b_j` be the corresponding coefficients conditional on an ordinary hub.
One-coordinate balance, applied after fixing one of the pair variables, gives

`q*a_1+u*b_1=0`, hence `b_1=-(q/u)*a_1`.

All the `a_j,b_j` for `j<=4` are bounded uniformly in `d` at fixed `K`. Indeed
they are expectations of fixed-order discrete differences of the bounded
normalized conditional row function. Thus `b_1=O_K(q)` while the other
coefficients are `O_K(1)`.

Multiplying the five row expansions gives an especially simple exact formula.
A pair variable must be selected at both ends or neither, since a single
centered factor has mean zero. Consequently the conditional moment, with
`c=a` or `c=b` according to hub type, is

`sum_(F subset E(K_5), F has no isolated vertices)
   (qu)^|F| product_(i=1..5) c_(deg_F(i))`.                 (1)

This formula sums **all** allowed pair graphs; no unaccounted higher-order
terms are dropped.

## 3. The negative fifth-order activity

A graph on five vertices with no isolates has at least three edges. The
three-edge graphs are exactly `P_3 disjoint_union K_2`: choose the degree-two
vertex and its two neighbours, giving `5*binom(4,2)=30` choices. Formula (1)
therefore gives, at a rare hub,

`M_5^rare=30*a_1^4*a_2*(qu)^3+O_K(q^4)`.

At an ordinary hub, a three-edge term has four leaves and is `O_K(q^7)`.
A four-edge graph without isolates has at least two leaves, so its term is
`O_K(q^6)`. Terms with at least five edges are `O_K(q^5)` already. Hence

`M_5^ordinary=O_K(q^5)`.

After averaging the hub type the exact moment satisfies

`M_5=E product_(i=1..5)g_(y_i)
    =30*a_1^4*a_2*u^3*q^4+O_K(q^5)`.                    (2)

These remainders are uniform because (1) is a finite sum over graphs on a
fixed five-vertex set and the coefficient bounds above are uniform.

Set `lambda=1/K`. As `d` tends to infinity,

`a_1=lambda/(1+lambda)+O_K(1/d)`,
`a_2=(1-lambda)/(1+lambda)+O_K(1/d)`.

Thus

`M_5/q^4 -> 30*lambda^4*(1-lambda)/(1+lambda)^5 > 0`.

In the raw iid polymer expansion the connected-set activity is
`w(S)=(-1)^|S| E product_(y in S)g_y`. Every five-star is connected in the
dependency graph, and therefore its activity is **negative for sufficiently
large d**. Eventual positivity of `M_5` is all that is needed; no assertion
for every dimension is inferred from this asymptotic.

## 4. The rooted negative load diverges

Fix one odd root `y`. There are exactly

`d*binom(d-1,4)`

five-stars containing it: choose the hub from its `d` neighbours and four
other neighbours of that hub. There is no duplication. Three distinct
neighbours of an even hub determine it uniquely, since the second common
neighbour of the first two is at distance three from the third.

Combining this count with (2), for sufficiently large `d` gives

`sum_(five-stars S containing y) max(0,-w(S))
  = (5/4)*(1-lambda)*lambda^8/(1+lambda)^5 * d + O_K(1)`. (3)

The coefficient is strictly positive. Given any fixed positive small
bad-probability allowance, choose `K` sufficiently large. Then (3) still
diverges in `d`, even along dimensions that are powers of two. Consequently
no dimension-uniform bound on this raw negative root load follows just from
small probability, symmetry and exact one-coordinate balance.

The same leading term occurs for fifth cumulants. The analogous two- and
three-centre graph expansions give

`M_2=q^2*a_1^2`, `M_3=O_K(q^3)`.

All individual iid means vanish; the five-star is symmetric, so

`kappa_5=M_5-10*M_2*M_3=M_5+O_K(q^5)`.

Thus its signed fifth-cumulant load has the same obstruction. This assertion
does not replace the actual polymer activities by cumulants in a partition
identity where such a replacement has not been justified.

## 5. Uniform injective sampling

The five-star union contains `h=5d-14` distinct even source vertices. Its
marginal under a uniform injection of `E` into `Omega` is the uniform ordered
sample of `h` distinct labels. Compare it with iid sampling conditioned on
local distinctness. Since `p<1/2`, all the normalized factors have absolute
value at most one, and

`|E_inj product g_y - E_iid product g_y| <= h*(h-1)/N`.

This follows by conditioning and the union bound on iid collisions. Summing
over rooted five-stars incurs an error `O(d^7/N)`, tending to zero when
`N>=C*2^(d-1)`. The finite partition formula for a fifth cumulant gives the
same error order for cumulants; any nonzero injective single means are
included in that comparison. Therefore (3) transfers to these local injective
moments and cumulants.

Iid independent-component factorization does **not** thereby become an exact
factorization under injections. Nor is exact iid coordinate balance being
claimed for the conditioned injection law.

## 6. Even type-distribution minimization does not remove this example

For the fixed weighted type relation `W`, allow its rare probability to vary
from `q` to `z`, keeping `w` fixed. Its bad probability is

`P(z)=Pr(Bin(d,z)>=3)+w*(1-z)^d`.

Direct differentiation gives

`P'(z)=d*(1-z)^(d-3)*[binom(d-1,2)*z^2-w*(1-z)^2]`.

Because `w=binom(d-1,2)*(q/(1-q))^2`, this derivative is negative for `z<q`
and positive for `q<z<1`. Thus `q` is the global minimizer over two-type
probability distributions. This is stronger than mere stationarity for that
**weighted type problem only**. It says nothing about minimization over all
full tag distributions in the zero-one lift, let alone the original Ramsey
edge-fugacity functional. Those distinct minimization claims are not used.

## 7. These examples have avoiding injections

For fixed `K`, sufficiently large even `d`, and `N=KdL*s>=4m`, where
`m=2^(d-1)`, there is an explicit injection of `E` into `Omega` making every
odd neighbourhood good. This prevents misreading (3) as a packing disproof.

Let `k=ceil(log_2 L)` and assume `k<=d/2`, which holds eventually. Choose `k`
independent binary characters on `E`, each represented by a subset of the
`d` coordinates of size `d/2`. One explicit choice is a fixed half `A`, then
`A symmetric_difference {a,b_j}` for a fixed `a in A` and `k-1` distinct
`b_j` outside `A`. Their representing vectors are independent, and leave an
outside coordinate unused, so their span does not contain the all-ones
vector. They therefore remain independent on `E`.

Write their bit values as `beta_j(x)`. For every odd `y` and every `j`,

`sum_(x adjacent y) beta_j(x)=d/2`.

Define the tag of an even vertex by

`tag(x)=tau+sum_(j=0..k-1) 2^j*beta_j(x) mod L`.

Every row tag sum is consequently

`d*tau+(d/2)*(2^k-1) mod L`.

Since `gcd(d,L)=1`, choose `tau` to make this residue equal to `r`, which is
outside the bad residue interval `{0,...,r-1}`. Use only ordinary types.

It remains to assign distinct full labels. Character independence implies
that every bit pattern occurs exactly `m/2^k` times. Thus each tag is required
at most

`ceil(2^k/L)*m/2^k <= 2m/L`

times. There are `(Kd-1)*s=(1-q)*N/L>2m/L` ordinary full labels with each
fixed tag. Choose distinct type/copy pairs within each tag fibre. The result
is an injection, has no rare labels, and has a good tag sum at every row.

## 8. Verification and remaining Ramsey gap

A separate agent independently audited the balance, coefficient formulas,
graph-cover exponents, root constant and injective comparison. The parent
then implemented `check_cube_balanced_negative_star.py`, with transcript
`CubeBalancedNegativeStarVerification.txt`. The checks include all 1,024
shared-type assignments for each conditional five-star in four parameter
cases, independent finite-difference coefficient evaluations, enumeration of
all pair-graph covers, exact rational moment/cumulant signs, and the character
ranks, tag sums and fibre capacities in the avoiding construction. The
asymptotic conclusion rests on (1)--(3), not on the finite checks.

The signed-partition positivity theorem itself remains valid. What fails is
this proposed way of verifying its negative-activity hypothesis uniformly
from balance alone. A compatible resummation, a stronger hypothesis connected
to the original graph, or another complete Hall-capacity argument is still
needed. **Neither theorem in `Spec.lean` is proved.**

### Additional original-graph check

The displayed relation cannot literally be the empty-common-neighbour
relation of any bipartite graph on all tuples (including repetitions).
For any rare full label `a`, the tuple `(a,...,a)` is bad. Such a graph
representation would force the neighbour set of `a` to be empty, and
therefore every tuple containing `a` would be bad. But a tuple containing
exactly one rare label and otherwise ordinary labels is good by definition.
This is a direct contradiction, independent of the number of candidate
vertices. Thus the construction is not an original-graph counterexample.
This check does not rule out representing the restriction to distinct tuples,
nor show that changing repeated-tuple values preserves exact balance or
supplies a graph representation with only a linear number of candidates.
