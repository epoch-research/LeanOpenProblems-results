# Independent audit of the buffered-coloring argument

## Verdict

I find **no mathematical gap or counterexample in the supplied buffered proof**, including its support-locality lemma, arbitrary-width surgery, and localized induction. Reconstructing those arguments independently gives the stated finite witness theorem. The proposed recursive-radius replacement also works and is a simpler route to formalizing a disproof of the stated Erdős 74 proposition.

This is a mathematical audit, **not a completed Lean certification or a literature-priority determination**. The graph-theoretic lemmas remain to be formalized. The current problem page could not be fetched because DNS resolution failed. No claim about current published resolution follows from the literature checks.

## 1. Cut parity and the sparse certificate

For a map `p : V -> F_2`, not necessarily a proper coloring, the bad-edge indicator is `1 + p(u) + p(v)`. Summing on a cycle proves the parity condition. The minimum number of bad edges equals the minimum number of edges whose removal makes the graph bipartite: one inequality deletes the bad edges; the other properly colors the graph after a minimum deletion and observes that every bad edge belongs to the deletion set.

The search-tree certificate is valid. Every node at depth less than `k` has a failing short cycle because its selected set has fewer than `a_L` edges. Along a putative cut `A` of the union graph with fewer than `k` bad edges, maintain `D subset A`. The two parities on the selected cycle differ, so `(A minus D)` meets it and supplies a child. Each step adds a new edge. This contradicts `|A| < k` after `k` steps.

There are at most `1 + L + ... + L^(k-1)` selected cycles and at most `L + ... + L^k <= 2 L^k` vertices in their union. The vertex set must be the union of the cycle vertex sets, not the ambient vertex type including isolated vertices. All selected edges are original edges.

The sentence allowing a childless node is harmless: a failed parity equation actually implies the cycle is not wholly contained in `D`, so such a node cannot occur here.

## 2. Support locality

Let `A` be an auxiliary component contained in `S` and disjoint from `F`. Every short cycle touching `A` has all its `F union S` edges in that component. It therefore has no `F` edge and is even, by cut parity. All its `S` edges are in `A`, so it meets `A` evenly. Cycles not touching `A` are unchanged. Thus `S minus A` still solves every equation, contradicting minimum cardinality.

Consequently every `S` edge has an auxiliary path to `F`. Stop at the first `F` edge and take a simple path. Its preceding vertices are distinct elements of `S minus F`, so it has at most `s` steps. Each step is realized within an original short cycle, with endpoint distances at most `L`. This proves `V(S) subset N_(sL)(V(F))`.

There is no assumption of bounded degrees or bounded neighborhood cardinalities. Minimum cardinality, or sufficient inclusion-minimality, is essential: in a forest with a proper cut, `F` is empty while an arbitrary nonempty `S` satisfies every short-cycle equation and violates locality. This is a counterexample to a weakened lemma, not to the stated one.

## 3. Buffered surgery

### Consistency of the terminal constraints

Put `D=2r+4`. Every auxiliary edge traces an original walk of length at most `D`. An auxiliary simple cycle has at most `|W|` edges; this includes a parallel-edge cycle of length two. Its traced closed walk therefore has length at most

`D |W| <= D * 2(t+s) <= 4tD = 8t(r+2) <= L`.

The sum of its labels is the sum of `1+1_S` on that closed walk, counting multiplicities. Decompose it into original simple cycles and doubled edges. Every simple cycle in the decomposition has length at most the closed walk's length, hence at most `L`; its sum is zero by the hypothesis. A doubled edge contributes zero over `F_2`. All auxiliary cycles are balanced, and the labels integrate on each component to `q`.

The close-terminal constraints imply that `q+p_0` is constant on every terminal pair at `P`-distance at most `D`. Thus `d_P(X,Y) > D`. No integration on the full original graph is asserted or needed.

### Interpolation and arbitrary width

An equivalent description of the table is:

* remove the vertices with `p_0(v)=1` in distance layers `r+2` and `r+3` from `X`;
* on the surviving vertices of distance at most `r+2`, flip `p_0`;
* leave the other surviving vertices unchanged.

Edges within either phase remain proper. An edge crossing the interface from layer `r+2` to layer `r+3` has a `p_0=1` endpoint, which was removed. All other possible adjacent-layer configurations also give different colors. This proves the table without any restriction on `r` beyond `r>=0`.

Terminals in `X` are flipped; terminals in `Y` have distance at least `2r+5`, so are not flipped. All terminals survive and receive `q`. The residual bad edges are exactly `S`.

### Distances in the original graph

For a removed vertex `z`, the interpolation gives

`r+2 <= d_P(z,W) <= r+3`.

The lower bound to `Y` follows by concatenating paths with a shortest path from `z` to `X`: a shorter route to `Y` would contradict `d_P(X,Y)>=2r+5`.

The apparently dangerous passage from `P` back to `G` is valid. Every deleted edge in `F union S` has both endpoints in `W`. A `G` path from a vertex outside `W` to its **first** vertex of `W` therefore uses no deleted edge. In particular, distance to the set `W` is the same in `P` and `G`. This transfers the lower bound as well as giving the required upper bound in `G`.

All removed vertices have `p_0=1`, so they are independent in `P`. They avoid `W`, so no edge in `F union S` can join or even touch them. They are independent in `G` too.

The even-cycle equations cannot be omitted. On `C4`, use cut bits `(0,0,1,1)`, so `t=2`, and take `S` to be one edge. All odd-cycle conditions are vacuous and `s<=t`. But `W` is the whole vertex set, so the buffer conclusion forces `Z` empty, whereas no cut of an even cycle has exactly one bad edge. The actual hypothesis excludes this example via its even-cycle equation.

## 4. Localized induction and quantitative bounds

The induction is properly simultaneous over all finite graphs satisfying the hereditary no-witness property and all cuts with `t` bad edges. It is not restricted to minimum cuts. Vertex deletion gives an induced subgraph `G'=G-Z`, so the hereditary hypothesis and independence both transfer correctly.

The inductive set `I'` has an actual `G'` path of length at most `s^8<=r` to `V(S)` for each of its vertices. This is also a `G` path. If an edge joined `z in Z` to `i in I'`, it would give a `G` path of length at most `r+1` from `z` to `V(S)`, contradicting the surgery's lower bound `r+2`. Thus `Z union I'` is independent. Its complement is bipartite by the inductive conclusion. No compatibility of previous two-colorings, no arbitrary choice of a third-color class, and no chromatic-number preservation under deleting `Z` is being assumed.

For `s=0`, the inductive correction is empty; for `t=1`, one endpoint of the bad edge suffices. Both boundary cases are sound.

Support locality and surgery give radius `sL+r+3`. With `m=floor(sqrt(t))`, this is at most `mL+r+3`. The numerical checks in the manuscript are correct:

* `t=2,3`: radii `52,76`;
* `t>=4`: `mL+r+3 <= 26t m^9 <= 26t^(11/2) <= t^8`.

The witness estimate is also correct. If `a_L>=m+1`, the certificate has `q=tau(H)>=m+1>sqrt(t)`, hence `L<=24q^10`, and

`|V(H)| <= 2(24q^10)^q <= (q+1)^(16q)`.

The last bound allocates exponents `5q` for `24^q`, `10q` for `q^(10q)`, and `q` for the leading factor 2. This contradicts the no-witness hypothesis and gives the strictly smaller cut count required for induction.

The finite witness theorem, its contraposition, and the infinite-graph deduction by finite-color compactness therefore follow. The estimates for all three displayed profiles in Section 6 also check out, including the initial zero intervals and `B(15)=2^960`.

## 5. Proposed recursive-radius replacement

Use, for positive `t`,

`R(0)=0`,

`L(t)=8t(R(t-1)+2)`,

`R(t)=t L(t)+R(t-1)+3`,

`B(t)=2 L(t)^t`.

This is exactly the proposed recurrence. Both `R` and `L` are strictly increasing, `L(t)>=16t`, and `B` is strictly increasing and unbounded. Define

`f(n)=min {t>=1 : n<=B(t)} - 1`.

Then `f` is nondecreasing, divergent, and `f(B(t))=t-1`. If only the inequality `f(B(t))<t` is stipulated for some other budget, monotonicity of `f`, or its equivalent bound throughout each interval `n<=B(t)`, must also be required.

Suppose every finite subgraph obeys the budget. For a cut count `t>=2`, the alternative `a_(L(t))>=t` yields an actual subgraph `H` with

`tau(H)>=t` and `|V(H)|<=B(t)`.

But its allowed budget is at most `f(B(t))=t-1`. Hence the minimum support has `s<t`.

Take `r=R(t-1)` for surgery. The inductive correction is within radius `R(s)<=r` of `V(S)`, so the exact same separation proof reuses color three. Its total radius is at most

`s L(t)+R(t-1)+3 <= (t-1)L(t)+R(t-1)+3 <= R(t)`.

The final inequality even has slack `L(t)`. The base cases require no change. This establishes the simplified proof with no square-root or real-logarithm arithmetic. The no-witness version also follows because `B(t)<=B(tau(H))` when `tau(H)>=t`.

For an indexing check:

* `R(0),R(1),R(2),R(3) = 0,19,694,50809`;
* `B(1),B(2),B(3) = 32,225792,9321620963328`.

The simplified argument is enough for the disproof target; it does not by itself prove the manuscript's sharper explicit `(t+1)^(16t)` bound. Its inverse budget is slower asymptotically.

## 6. Cross-checks and tests

* `K4` has frustration 2 and is an immediate witness.
* `M(K3)` has frustration 3 and chromatic number 4, but contains small frustration witnesses. It defeats an arbitrary-core third-color argument, not the localized induction used here.
* `M(C5)` has order 11 and frustration 4. The independent exact-cut calculations agree with these values.
* Arbitrarily long odd cycles, and unions of two such cycles with total frustration 2, rule out bounds based on frustration alone. They are three-colorable and do not contradict the chromatic-number-four theorem.
* Expanding projective-plane quadrangulations refute polynomial witness bounds. A lower witness of order `log(n)/log(log(n))` is compatible with their logarithmic hereditary upper estimates; the manuscript never asserts a polynomial bound. Known large-odd-girth Mycielski constructions likewise give no contradiction.
* Known constructions with arbitrarily slowly increasing chromatic numbers of finite subgraphs do not bound their edge frustration. These are different hypotheses.

The supplied checker was rerun successfully. In addition, `/tmp/audit_erdos74_independent.py` was independently written, without importing the supplied checker. It exhausts short-support choices on small weighted base graphs, expands them to actual subdivided graphs, and checks surgery under the actual short-parity hypothesis. It does not discard unbalanced auxiliary instances: such an instance would fail the test.

Results: 365 instances, 354 strict support descents, 143 supports violating some long-cycle parity equation, 302 nonempty buffers, 23 cases where the support is farther than `r+3` from the old bad endpoints, and largest graph order 12,981. All passed. The recurrence inequalities were also checked through `t=400`. The log is `/tmp/audit_erdos74_independent.log`.

These tests are consistency checks. The supplied random arbitrary-support tests, which skip unbalanced cases, are not by themselves evidence for the implication from short parity to balanced auxiliary labels. The closed-walk proof above supplies that implication.

## 7. Lean formalization requirements, not mathematical repairs

1. Prefer the recursive-radius version for a first formal disproof.
2. Use `SimpleGraph.edist : V -> V -> ENat`, or bounded-walk reachability. Mathlib's natural-valued `SimpleGraph.dist` is **zero for disconnected vertices**, unlike the infinity convention in the manuscript. Blindly translating its distance inequalities using `dist` would be wrong, especially when `X` is empty.
3. A two-coloring with bad edges is an arbitrary map to two bits, not a proper `SimpleGraph.Coloring`.
4. Keep `F` and `S` as sets of unordered original edges. Prove the elementary equality between minimum cut defects and edge-deletion frustration.
5. Formalize closed-walk parity with multiplicities, and handle parallel auxiliary constraints. Do not replace short even-and-odd cycle equations by odd-cycle hitting.
6. Quantify the induction over all finite graphs and all cuts of the given size. Use induced vertex deletion and explicit embeddings for `S`, paths, and subgraphs.
7. The certificate must be a genuine subgraph on its cycle-union vertices, not a spanning graph counted on the ambient type.
8. To connect to `Spec.lean`, show the set defining each fixed-`n` supremum is bounded (for example by `n*(n-1)/2`), so its supremum bounds each finite-subgraph frustration. Finite vertex sets also make all deletion sets finite. Finite-color compactness is available as `SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom` in `Mathlib/Combinatorics/SimpleGraph/Finsubgraph.lean`, applied with the finite complete graph on three colors.

No substantive correction to the mathematics of the supplied proof is required by this audit. Formalization is warranted; claiming that the current Markdown or Python tests already constitute a Lean proof is not.
