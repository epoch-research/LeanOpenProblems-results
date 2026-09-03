# Support steering fails: a tight-set obstruction, already for a three-edge path

**Conclusion.** The proposed support-steering statement is false. For every
`r >= 2` there is a simple r-circuit G and an actual tree F with
`|E(F)| = 2r-1` and `Delta(F) = r` such that **every** spanning map P avoiding
F leaves a vertex of F outside **every** `(r-1)`-circuit of `G-P`.
This applies a fortiori to colors in compatible full decompositions.

At `r=2`, F is a three-edge path. At `r=3`, F is the five-edge double star
with two adjacent degree-three vertices. The same host already gives a
counterexample with only `r+1` protected edges.

Nevertheless, a compatible full decomposition avoiding F exists, even with
the extra edge incident to a maximum-F-degree vertex. An explicit such
decomposition is given below. Thus neither global edge protection nor
pinned surplus is contradicted; what fails is keeping all protected
vertices/edges in the lower circuit.

All arguments are finite graph arguments, not Lean formalizations.
`Submission/Spec.lean` was not modified. This is not a counterexample to
Erdos--Sos.

## 1. The exact tight-set restriction

Let `q=r-1`, and suppose

    G = P disjoint-union Q_1 ... disjoint-union Q_q disjoint-union {e}

is a full decomposition into spanning maps and one extra edge. Set
`H=G-P`, and let C be its unique q-circuit, as in the rooted lower-circuit
lemma in `ErdosSosCircuitFindings.md`.

Let T be the vertex set that C is required to contain, and suppose P avoids
the protected edge set F. For any proper vertex set S with `T not subset S`,
put

    d_r(S) = r|S| - e_G(S) >= 0.

Since C cannot be contained in S, `H[S]` is q-independent, so

    e_H(S) <= q|S|,
    e_P(S) = e_G(S)-e_H(S) >= |S|-d_r(S).                 (1)

On the other hand, `P[S]` is a pseudoforest contained in `G[S]-F`. Let
`t(S)` count the acyclic connected components of `G[S]-F`, **including
isolated vertices**. A tree component on a vertices contributes at most
`a-1` edges to a pseudoforest, and any other component contributes at most
a. Consequently

    e_P(S) <= |S|-t(S).

Thus a necessary support-steering condition is

    t(S) <= d_r(S)       whenever T not subset S.         (2)

In particular, if S is **r-tight**, `e_G(S)=r|S|`, then `P[S]` must be a
spanning map on S. Hence every component of `G[S]-F` must contain a cycle.
An isolated vertex in `G[S]-F` is already a rigorous obstruction.

Equivalently, if S is r-tight and protecting F isolates a vertex inside S,
then every compatible lower circuit lies entirely inside S, whether or not
F has a vertex outside S. Indeed, `e_P(S)<=|S|-1`, so
`e_H(S)>=q|S|+1`; the unique circuit of H must be contained in S.

This restriction concerns the complement color on a host tight set. The
abstract tree identity involving `c(F-U)+e_F(U)` does not imply it.

## 2. The counterexample family

Fix `r>=2`. Let

    W = {0,1,...,2r},       A = {0,1,...,r-1},
    u = 2r+1,              v = 2r+2.

Construct G from the complete graph on W by adding

    ua, va  for every a in A,       and uv.

In particular,

    d_G(u) = d_G(v) = r+1.

### G really is an r-circuit

Its order is `n=2r+3`, and

    e(G) = binom(2r+1,2)+2r+1 = r(2r+3)+1 = rn+1.

For a proper vertex set S, put `t=|S intersect W|` and
`k=|S intersect {u,v}|`.

If `k<=1`, then

    e_G(S) <= binom(t,2)+kr <= rt+kr = r|S|.

If `k=2`, properness gives `t<=2r`. For `t=0`, there is only the edge uv.
For `1<=t<=2r`,

    rt-binom(t,2) = t(2r+1-t)/2 >= r,

and therefore

    e_G(S) <= binom(t,2)+2r+1
           <= rt+r+1
           <= r(t+2).

This verifies every proper induced-set inequality. The only nonempty
proper r-tight sets are W, `W union {u}`, and `W union {v}`; the same
estimates are strict in all other cases for `r>=2`.

### The protected tree

The smaller obstruction is the tree

    E(F_0) = {ua : a in A} union {0v}.

It has `r+1<=2r-1` edges and maximum degree r. To reach exactly the proposed
size and obtain the two-branching-vertex shape, set

    B = {r,r+1,...,2r-3},       |B|=r-2,
    E(F) = E(F_0) union {0b : b in B}.

For `r=2`, B is empty. The centers u and 0 are adjacent. Each has `r-1`
other neighbors in F, and these neighbor sets are disjoint. Thus F is the
adjacent double r-star, with

    |V(F)|=2r,       |E(F)|=2r-1,       Delta(F)=r.

For `r=3`, explicitly,

    E(F) = {70,71,72,08,03},

with centers 7 and 0 and leaves 1,2,8,3.

### Why no spanning-map deletion can work

Let P be **any** spanning map of G avoiding `E(F_0)` (and hence this applies
to any P avoiding F).

1. All r edges from u to A are protected. A spanning map has no isolated
   vertices. Therefore `uv in E(P)` and `d_P(u)=1`.
2. If `d_P(v)=1` also, the component of P containing uv would be the
   two-vertex one-edge tree, not unicyclic. Consequently `d_P(v)>=2`.
3. Thus

       d_(G-P)(v) <= (r+1)-2 = r-1.

Every q-circuit has minimum degree at least `q+1=r`: deleting any vertex
from its circuit inequalities gives

    q|C|+1-d_C(x) <= q(|C|-1).

So v belongs to **no** q-circuit in `G-P`. But v is a vertex of both F_0
and F, and `0v` is a protected edge. Support steering is impossible.

This degree proof does not even require P to be compatible with a full
decomposition or the lower circuit to be unique.

The tight-set proof exposes the structural source of the same obstruction:
`S=W union {u}` is r-tight, `v notin S`, and u is isolated in `G[S]-F_0`.
Condition (2) fails with `t(S)=1` and `d_r(S)=0`. In every compatible
decomposition the unique lower circuit must be contained in S.

## 3. Full compatibility and maximum-degree surplus pinning are still possible

Here is an explicit decomposition for every r. Arithmetic on W is modulo
`N=2r+1`. For `i=1,...,r`, let

    E(R_i) = {{j,j+i} : j in W}.

The R_i partition `K_N`. Each is a spanning 2-factor: its components are
cycles of length `N/gcd(N,i)`, which is at least three.

Take the red map

    P = R_1 union {uv,v1}.

It consists of a Hamilton cycle on W with the pendant path `1-v-u`.
It avoids F: it uses none of `uA` or `0v`, and the extra protected edges
`0b`, `b in B`, are not cycle edges of R_1.

For `i=2,...,r`, define

    b_i = 0 if i=2, and b_i=i-1 otherwise,
    Q_(i-1) = R_i union {u(i-2), v b_i}.

Each Q is a spanning map: it adds u and v as pendant vertices to a
spanning 2-factor on W. Finally let

    e = u(r-1).

These r maps and e partition all of `E(G)`. The extra edge is incident to
u, a vertex maximizing `d_F`, and also maximizing `d_(F_0)`.

The resulting lower circuit is exactly on `W union {u}`. To see this,
orient R_i by `j -> j+i`, orient each pendant edge away from u or v, and
orient the extra edge away from u. In H the outdegrees are q everywhere
except u, whose outdegree is `q+1`. Vertex u reaches 0 via Q_1, and the
`+2` cycle R_2 reaches every vertex of W because N is odd. There are no
arcs from W or u into v. Thus the reachable set is exactly `W union {u}`,
and the rooted lower-circuit lemma identifies its induced graph as the
unique q-circuit. In particular, the extra-edge pin works but `0v` is
retained only as an edge outside the lower circuit.

## 4. The smallest displayed instance: a three-edge path

For `r=2`, take

    V(G) = {0,1,2,3,4,5,6},
    E(G) = E(K_5 on {0,1,2,3,4}) union {05,15,06,16,56},
    F = the path 1-5-0-6.

Then `e(G)=15=2*7+1`, `|E(F)|=3`, and `Delta(F)=2`.
Every avoiding spanning map must use 56 and 16. Hence vertex 6 has degree
one in `G-P`, excluding it from every bicircular circuit.

An explicit compatible decomposition, with extra edge at the
maximum-F-degree vertex 5, is

    P = {01,12,23,34,40,16,65},
    Q = {02,24,41,13,30,50,60},
    e = 51.

Both P and Q are spanning unicyclic graphs. The lower circuit consists of
the cycle `0-2-4-1-3-0` and the path `0-5-1`; vertex 6 is a leaf of H
attached by the protected edge 06, not a circuit vertex.

For comparison, G itself does contain a bicircular circuit containing F:
the `K_4-56` on `{0,1,5,6}`, with edges `{01,05,15,06,16}`. The problem is
its incompatibility with the required complementary spanning map, not an
absence of lower circuits containing that path in the original graph.

## 5. Exact verification

Run from `/workspace/leanproject`:

    python3 Submission/ErdosSosSupportSteeringChecks.py --atlas

The checker uses no random sampling. It verifies:

* All proper induced-set inequalities for the host and the explicitly
  constructed lower circuit, for `r=2,...,6`, for both protected trees:
  10 host/lower-circuit pairs. It also verifies the precise three
  nonempty proper tight sets.
* The explicit decomposition, protected tree, pinned extra edge, quota
  orientation, and exact reachable lower-circuit support for
  `r=2,...,30`, for both protected trees: 58 protected-tree/decomposition
  instances (the two trees use the same decomposition).
* Every one of the 792 candidate seven-edge red subsets avoiding the
  displayed three-edge path. Exactly 222 are spanning maps, and 204 are
  compatible. None can put vertex 6 in a lower circuit. Compatibility is
  cross-checked independently by trying every possible extra edge;
  the removable-extra-edge set is exactly the computed bicircular circuit.
* Every path of lengths one, two, and three in all 31 atlas 2-circuits
  (order at most seven), enumerating all possible red maps and compatible
  lower circuits. There are respectively 461, 1,599, and 4,355 distinct
  path edge sets. All one- and two-edge paths pass; exactly six three-edge
  paths fail, distributed over two seven-vertex hosts. Every failure has
  an r-tight set missing a protected vertex in which protection isolates
  another vertex, exactly the certificate of Section 1. Both failing hosts
  are a K_5 plus two adjacent degree-three vertices. This is a finite pilot
  result, not a theorem for paths of length two on arbitrary hosts.

The original `ErdosSosCircuitChecks.py` also passes unchanged.

Separate direct subset enumeration, without the existing circuit-checker
functions, also verifies the `r=2` and `r=3` hosts, tight sets, and protected
paths/double stars.

The SHA-256 of `Spec.lean` remains

    674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103.

**Scope.** This disproves the exact proposed support-steering lemma,
including the nonspanning version and even with maximum-degree surplus
pinning. It does not disprove Erdős--Sós, the global protection theorem,
or the pinned-surplus lemma. A replacement statement must at least
address restriction (2), or allow changing the prescribed embedding F.
