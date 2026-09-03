# Constant-loss ordinary cubes rule out the parity-pentagon candidate

## Status

This resolves the **asymptotic counterexample question for this specific family**, not Erdős 181. Every parity-pentagon colouring on `5^t` vertices has an ordinary injective red cube on more than `5^t/10` vertices, for `t>=1`. For even `t` the stronger fraction `1/4` holds. Therefore this family cannot disprove `R(Q_d)=O(2^d)`.

The key is to combine many coordinate directions into a *whole red clique*, instead of only using one-coordinate Hamming edges. The resulting embeddings need not be affine in the source binary bits, so they do not contradict the audited affine bound `d<=2t`.

## 1. Two complementary monochromatic subspaces

Recall the host `F_5^t`, with sign

`S_t(x,y) = product_i h(x_i-y_i)`,

where `h(0)=h(1)=h(-1)=+1`, `h(2)=h(-2)=-1`, and a distinct pair is red when its sign is `+1`.

Take `t=2k`. Regard a host vector as `(x,y)` with `x,y in F_5^k`. Define

`L_+ = {(a,a): a in F_5^k}` and `L_- = {(b,-b): b in F_5^k}`.

Each is a red clique: differences in either subspace have paired coordinates, and `h(z)=h(-z)`, so their sign is `product_i h(z_i)^2=1`. The two subspaces are complementary because 2 is invertible in `F_5`.

In particular the bijection

`Psi(a,b) = (a+b,a-b)`

exhibits a spanning red subgraph isomorphic to

`K_(5^k) square K_(5^k)`.

Indeed, if only `a` changes, the host difference is `(a-a',a-a')`; if only `b` changes, it is `(b-b',-(b-b'))`. Both signs are 1, with distinct endpoints. Non-required edges can have either colour; the embedding is not claimed to be induced.

This is much larger than the coordinate Hamming subgraph `K_5 square ... square K_5`: an edge may change many `a` or many `b` coordinates at once.

## 2. Nonlinear binary encoding

Let `s=floor(log_2(5^k))`, equivalently the largest integer satisfying `2^s<=5^k`. Choose any injection

`E: {0,1}^s -> F_5^k`.

For example, interpret the binary word as its integer in `[0,2^s)` and write that integer in base 5 with exactly `k` digits.

Define the map on the `2s`-cube by

`F(u,v) = (E(u)+E(v), E(u)-E(v))`.

It is injective: equality of its two coordinate blocks implies equality of `2E(u)` and `2E(v)`, hence equality of `E(u),E(v)` and then of `u,v`. A source edge changes exactly one bit in `u` or in `v`; regardless of how many base-five digits change, its host difference belongs to `L_+` or `L_-`. Thus every required edge is red.

Consequently, for all `k>=0`,

`D^R_(2k) >= 2 floor(k log_2 5)`.

Since `2^s > 5^k/2`, the image size satisfies

`2^(2s) > 5^(2k)/4`.

There is at most one bit of deficit relative to the cardinality upper bound:

`floor(2k log_2 5) - D^R_(2k) <= 1`.

## 3. Odd number of host coordinates

For `t=2k+1`, append one host coordinate in `{0,1}` and one source bit `w`:

`F_odd(u,v,w) = (E(u)+E(v), E(u)-E(v), w)`.

Internal edges are as above and have last-coordinate difference zero. An edge in `w` changes only the last coordinate by `+/-1`, which has sign 1. Injectivity is immediate. Hence

`D^R_(2k+1) >= 2 floor(k log_2 5)+1`,

and

`2^(2s+1) > 2*5^(2k)/4 = 5^(2k+1)/10`.

This includes `t=1`, where it is just a red edge of the pentagon.

Thus **for every `t>=1`, the original colouring contains a red cube of order greater than `5^t/10`**. If this host avoids `Q_d`, then `d` must be greater than the constructed dimension, so

`5^t / 2^d < 5`.

For even `t` the corresponding bound is `<2`. Neither bound is asserted as an upper bound for arbitrary colourings.

## 4. What this settles and what it does not


- It rules out an unbounded Ramsey ratio in the entire audited parity-pentagon family.
- It gives ordinary cubes above the affine maximum: at `t=8`, `k=4`, `s=9`, the construction is a red `Q_18`, whereas every affine binary subset-sum injection has dimension at most 16.
- It explains exactly why the Hamming-fibre surplus was not an upper bound: the new edges can change many coordinates within one entire red subspace.
- It does not decide every exact dimension; for instance it still gives `Q_8`, not `Q_9`, at `t=4`. Exact finite dimensions are unnecessary for ruling out the asymptotic candidate.
- It does not settle Erdős 181 or justify changing either theorem proof in `Spec.lean`.

## 5. Generalization

The same argument works for every finite abelian group `A` of odd order and any symmetric sign function `h:A->{+1,-1}` with `h(0)=1`. Multiplication by 2 is an automorphism; pairing coordinates produces the complementary red cliques `{(a,a)}` and `{(b,-b)}`. For the even parity-tensor powers on `A^(2k)`, there is an ordinary red cube of order greater than `|A|^(2k)/4`.

No numerical extrapolation is used. `check_cube_parity_pentagon_resolution.py` verifies the explicit injections and all required edges in examples, including the nonlinear `Q_18` at `t=8`.

## 6. All fixed finite abelian base groups (including even order)

There is a further constant-loss construction when multiplication by 2 is not invertible. Let `G` be any fixed finite abelian group of size `q`, and let `r=|G[2]|`, where `G[2]={g:2g=0}`. Let `h:G->{+1,-1}` be symmetric with `h(0)=1`. For `t=2k`, `k>=1`, define two subgroups of `G^(2k)`:

`P={(a_1,a_1,a_2,a_2,...,a_k,a_k)}`,

`Q={(-b_k,b_1,b_1,b_2,b_2,...,b_(k-1),b_k)}`.

For `k=1` the second expression is `(-b_1,b_1)`. Each subgroup has size `q^k` and is a red clique, since its coordinates pair as equal or opposite values. The two pairings form one cycle. Solving the equalities in the displayed coordinates gives exactly

`P intersection Q = {(g,g,...,g): g in G[2]}`,

which has size `r` independent of `k`.

Choose one representative in `P` from each coset of `P intersection Q`; call their set `A`. The map `(a,b) -> a+b` from `A x Q` into `G^(2k)` is injective: equality of sums puts `a-a'` in the intersection, so the representatives agree, followed by `b=b'`. Changing only `a` gives a nonzero difference in `P`, and changing only `b` gives one in `Q`. Thus the original red graph contains

`K_(q^k/r) square K_(q^k)`.

Encoding arbitrary binary strings in the two clique factors gives a red cube with more than

`q^(2k)/(4r)`

vertices. For odd tensor powers, fix the last coordinate, losing at most the fixed factor `q`. Therefore **every fixed finite abelian Cayley-sign base has bounded Ramsey ratio in all its parity-tensor powers**, even without odd order. The bound is allowed to depend on the fixed base group; this statement does not control families where `G` itself grows.

## 7. Elementary abelian 2-group bases, even when the base grows

Every red-blue **Cayley** colouring on `V=F_2^s` contains a spanning monochromatic `Q_s`, regardless of whether it came from a tensor power. Here the colour of a distinct pair `x,y` must depend only on `x+y`. This hypothesis is not satisfied by an arbitrary colouring in `Spec.lean`.

Let `S,T` partition `V\{0}` into the two connection sets. At least one spans `V`. Indeed, if `H=span(S)` is proper, choose `v` outside `H`. Every point outside `H` lies in `T`; for every `h in H`, both `v` and `v+h` lie outside `H`, and their sum is `h`. Hence `span(T)=V`.

Choose a basis `b_1,...,b_s` from whichever connection set spans. The map `x -> sum_i x_i b_i` from the binary cube is a bijection onto `V`. Each coordinate edge has difference one of those basis vectors, so every required edge has the chosen colour. The case `s=0` is the single-vertex cube.

Thus the apparent growing-base gap in Section 6 does not yield a counterexample when the base is an elementary abelian 2-group: its parity-tensor powers are themselves Cayley colourings on an elementary abelian 2-group and have a spanning cube. This observation supplies no reduction of general colourings to Cayley colourings and no proof of Erdős 181.

## 8. Uniform constant for all even powers, with arbitrary growing abelian bases

Section 6's factor `|G[2]|` can in fact be removed if either colour is permitted. Let `G` be any finite abelian group of order `q`, let `t=2k>=2`, and let `h:G->{+1,-1}` satisfy `h(-a)=h(a)` and `h(0)=1`. Then the parity-tensor colouring on `G^(2k)` contains a monochromatic

`Q_(2 floor(log_2(q^k)))`,

and hence a cube on more than one quarter of its vertices. The constant is independent of the base group, so even-power families with growing bases are excluded too.

Use the subgroups `P,Q` from Section 6 and put `H=P+Q`. The homomorphism

`pi(z)=z_1-z_2+z_3-z_4+...+z_(2k-1)-z_(2k) mod 2G`

maps onto `G/2G`. It kills `P` and `Q`: on `P` the alternating sum is zero, and on `Q` it is `-2b_k`. Since `|P intersection Q|=|G[2]|=|G/2G|`, the subgroup `H` has exactly the same index as `ker(pi)`, so `H=ker(pi)`. Thus `V/H` is an elementary abelian 2-group of order `r=|G[2]|=2^s`.

Let `S` be the red connection set, and let `W` be the binary span of `pi(S)` in `V/H`. There are two cases.

**Case 1: `W=V/H`.** Choose red vectors `v_1,...,v_s` whose quotient images form a basis. Let `A` be a set of representatives in `P` modulo `P intersection Q`, so `|A|=q^k/r`. The map

`(a,b,z) -> a+b+sum_i z_i v_i`, for `a in A`, `b in Q`, `z in {0,1}^s`,

is injective. Quotient projection first determines `z`, and Section 6's coset argument then determines `a,b`. Changing only `a` gives a nonzero red difference in `P`; changing only `b` gives one in `Q`; flipping a bit of `z` gives `+/-v_i`, also red. Therefore the red graph contains

`K_(q^k/r) square K_(q^k) square Q_s`.

Encoding binary strings arbitrarily in the clique factors gives dimension

`floor(log_2(q^k/r))+floor(log_2(q^k))+s = 2 floor(log_2(q^k))`,

because `r=2^s`.

**Case 2: `W` is proper.** Choose a nonzero binary linear functional on `V/H` annihilating `W`. Its composite with `pi` partitions all host vertices into equal halves. Every difference across the halves has nonzero functional value, hence cannot be red. All cross pairs are therefore blue. This blue complete bipartite graph contains `Q_floor(log_2(q^(2k)))`, which is at least the required dimension.

This proves the stated result. It does not address an arbitrary non-tensor Cayley colouring, odd powers with growing bases, or the arbitrary colourings in Erdős 181. The elementary binary-Cayley case in Section 7 remains stronger when it applies.

### Exact construction audit for Section 8

`check_cube_even_parity_uniform.py` implements both quotient cases, rather than
searching for embeddings. For every symmetric sign function on each cyclic base
`Z/q`, `2<=q<=9`, and on `F_2^2`, at `k=1,2`, it checks the subgroup intersection,
coset representatives, the equality `P+Q=ker(pi)`, injectivity, dimension, strict
quarter-size bound, and the original colour of every required edge. All 136
colourings passed: 122 red-basis constructions and 14 blue-character constructions,
154,288 embedded vertices in total and 892,368 required edges. The transcript is
`CubeEvenParityUniformVerification.txt`. These finite checks audit the explicit
construction; the all-group conclusion rests on the preceding argument. They do
not prove either theorem in `Spec.lean`.
