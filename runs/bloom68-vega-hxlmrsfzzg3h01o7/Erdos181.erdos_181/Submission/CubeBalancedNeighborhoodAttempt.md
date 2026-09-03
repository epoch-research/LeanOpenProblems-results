# Symmetric balanced neighbourhood avoidance: exact intermediate results

## Scope and unresolved target

Let `X,Y` be the two parity classes of `Q_d`, each of size `m=2^(d-1)`, and let `H_d` have vertex set `X` and hyperedges `N_Q(y)` for `y in Y`. A coordinate-symmetric bad relation `B subset Omega^d`, with `|Omega|=N`, has iid-uniform probability `p` and is exactly first-coordinate balanced if `Pr(B | X_i=a)=p` for all `i,a`.

The investigated statement was whether absolute `C,p0>0` ensure an **injective** avoidance map `X -> Omega` whenever `N>=Cm` and `p<=p0` (initially for power-of-two `d`). It is NOT proved or disproved here. Even that statement would require further work on the actual graph-derived relations and Hall matching before it could imply the Ramsey theorem. `Spec.lean` is unchanged.

The first three results below were returned by the read-only research agent and checked mathematically by the parent. The later pair-generated theorem and fourth-order audit have separate reports.

## 1. Exact variance cancellation, not a proof of zero bad edges

For `g=1_B-p`, take the orthogonal Hoeffding decomposition `g=sum_S g_S`. Write `W_r=sum_(|S|=r) ||g_S||_2^2`. Balance gives `W_0=W_1=0`, symmetry gives `||g_S||_2^2=W_r/binom(d,r)`, and `sum_(r>=2) W_r=p(1-p)`.

Sample `F_x` independently and uniformly. Let `A_y` indicate badness of the tuple on `N_Q(y)`. Distinct neighbourhoods intersect in two vertices or are disjoint. Integrating their private variables shows exactly

`Cov(A_y,A_z)=W_2/binom(d,2)`

when they intersect, and zero otherwise. There are `binom(d,2)` intersecting neighbours of each `y`. Consequently, for `d>=2`,

`E Z=mp`, `Var Z=m[p(1-p)+W_2]<=2mp(1-p)`, where `Z=sum_y A_y`.

This is an iid statement, not a statement for uniform injections. It does not prove `Pr(Z=0)>0` when `mp` is large.

## 2. A fully injective small-p theorem

For `d>=2`, `N>=2m`, and `p<=1/(16d^2)`, an avoiding injection does exist.

Extend the source positions to `N` and sample a uniform bijection. For each bad injective assignment of one neighbourhood use its canonical permutation event, of probability `b=1/(N)_d`. Events are adjacent if their source or image sets intersect. The standard forcing-by-swaps coupling gives a negative-dependency graph: forcing one canonical event preserves every already true event disjoint from both its source and range, and the forced permutation is uniform conditional on that event. The full coupling/LLL proof is in `CubeAnchorCapacityRenewal.md`.

Put `beta=N^d/(N)_d`. Since `N>=2^d>=d(d-1)`, the iid collision union bound gives `beta<=2`. The total probability mass of canonical events involving a fixed source position is at most `beta*d*p`. Exact first-coordinate balance bounds the mass involving a fixed target value by `beta*m*d*p/N`.

Therefore the neighbouring probability mass of each event is at most `beta*d^2*p*(1+m/N)<=4d^2p`. Set its LLL weight to `2b`. Neighbouring weights sum to at most `8d^2p<=1/2`, so the product of their complements is at least `1/2`. Hence the lopsided local lemma applies. The sample is already a bijection, so its restriction is the required injection. No collision-removal step is omitted.

For `d=1`, exact balance and `p<1` imply that `B` is empty.

The factor `d^-2` remains; this is not a constant-p conclusion.

## 3. Constant-p avoidance for an actual translation-invariant subclass

Suppose `Omega=F_2^s`, `N=2^s`, and `B` is also invariant under simultaneous translations of all its coordinates. If

`p+(m-1)/N<1`,

then an avoiding injection exists. In particular `N>=2m`, `p<=1/2` suffice.

Choose independent uniform `a_1,...,a_d`. The vectors `a_i+a_d`, `i<d`, are independent uniform vectors; their probability of linear dependence is at most `(1+2+...+2^(d-2))/N=(m-1)/N`. Thus one can choose a good tuple with these differences linearly independent.

Define `F(z)=sum_i z_i a_i` on the binary cube. Its restriction to the even subspace is injective: for even `z`, `F(z)=sum_(i<d) z_i(a_i+a_d)`. At every odd `y`, its neighbourhood images are exactly `F(y)+(a_1,...,a_d)`, a translate of the chosen good tuple. All neighbourhoods therefore avoid `B`.

Translation invariance implies first-coordinate balance but is substantially stronger. There is no reduction from general balanced `B` to this subclass.

## 4. Pairwise independence does not determine all higher intersections

Let `q=2^t`, let `d>=4` be an even power of two with `t<=d-1`, and put `Omega=F_q x [L]`. Declare a tuple bad when the sum of its first coordinates is zero. Then `p=1/q`, symmetry and balance are exact, and the bad indicators of distinct neighbourhoods are pairwise independent.

Nevertheless, all `m` bad events occur together with probability `q^(-m/2)=p^(m/2)`, not `p^m`. Identify the odd and even classes by flipping coordinate 1. The neighbourhood matrix over characteristic two is `M=I+T_1+...+T_(d-1)`, where each `T_i` flips a coordinate. Splitting the last coordinate gives `M=[[D,I],[I,D]]` with `D^2=I`. Its rank is exactly `m/2`, proving the probability formula.

This is NOT an avoidance counterexample. Tag each even vertex by any `t` of its coordinates other than coordinate 1. Every tag fibre has size `m/q`; when `L>=m/q`, distinguish its vertices by their second coordinates to obtain an injection. At each odd neighbourhood the tag sum is the nonzero all-ones vector, so every neighbourhood is good.

## 5. Current additional results and the exact remaining gap

- `CubeBalancedPackingPairWitness.md`: if `B` means that some pair belongs to a fixed arbitrary symmetric relation `R`, exact balance and `p<=1/4` imply `Delta(R)<=24pN/[7d(d-1)]`. Graph packing of the cube's distance-two graph gives an avoiding injection for `N>=m`. This is a genuine constant-density subcase, not general `B`.
- The pair-cylinder core of general balanced `B` need not inherit balance. That report gives an explicit balanced zero-one relation with core maximum degree at least `pN/d`; it also gives explicit avoiding injections. Thus core deletion/conditioning cannot simply be declared harmless to the residual relation.
- `CubeBalancedStarExpansion.md`: a genuine symmetric balanced relation has bounded rooted pair mass but fourth-star absolute moment/cumulant mass `d/K^3+O_K(1)`, also under injection sampling. This refutes an absolute centered-cluster bound, NOT the negative-only positivity criterion. The parent's final section shows that the rare-hub contributions have nonnegative signed activities at every order.

No proof handles arbitrary remaining higher-arity bad relations, and no verified reduction eliminates the original graph/Hall constraints. Neither direction of the requested Lean theorem is established.
