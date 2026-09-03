# Independent B3 attack: exact Boolean defects and a Cartesian-code obstruction

## Status and scope

**The strong B3 conjecture is not resolved here.** No new asymptotic upper bound below the stated cubed constant 7/2, and no unbounded fixed-excess construction, is established. In particular, the results below must not be presented as a proof or disproof of `Erdos241.erdos_241`.

Two rigorous partial results are recorded:

1. An exact weighted collision identity for the Boolean indicator candidate associated with `2A-A`. It includes repeated summands, and identifies precisely what the Boolean condition asserts.
2. A sharp-exponent obstruction to literal Cartesian/additive-code amplification. Two B3 alphabets of size n cannot be combined into an almost n^2-element B3 code: the maximum is at most n^(4/3)+O(n). Coordinatewise multiset codes of arbitrary length have rate at most 2/3.

These are independent derivations for this attack, not claims of priority over the literature on separable codes or extremal bipartite graphs. The graph estimate and its sharpness construction are standard extremal-graph ingredients; their role here is to check the proposed amplification mechanism rigorously.

`Spec.lean` and `Reductions.lean` are unchanged. No theorem containing `sorry` is used as an assumption.

## 1. An exact Boolean certificate, including multiplicities

All statements in this section hold in an arbitrary abelian group. Convolutions are counting convolutions. A B2 or B3 condition always concerns **multisets**, not just subsets.

Let A be a finite B2 set of cardinality n. Write

- f = 1_A;
- S = A+A, regarded as a set;
- g = 1_S;
- r(x) = (g * 1_(-A))(x);
- h(x) = r(x) - (n-1) f(x).

Because A is B2, elements of S correspond bijectively to unordered pairs from A, with repetitions included. Thus r(x) counts the representations

    x = a+b-c,

with {a,b} an unordered multiset pair and c in A.

### Proposition 1

The function h is a nonnegative integer-valued function, h(a)=1 for every a in A, and

    sum_x h(x) = (n^3 - n^2 + 2n)/2.                 (1)

Moreover,

    A is B3  <=>  h(x) is in {0,1} for every x.      (2)

When these equivalent conditions hold, h = 1_(2A-A).

### Proof

If x is in A, the B2 property applied to a+b=x+c implies that {a,b}={x,c}. There is exactly one such pair for each c in A, so r(x)=n. Outside A, h=r is a nonnegative integer. Summing the convolution gives

    sum h = n |S| - n(n-1)
          = n * n(n+1)/2 - n(n-1),

which is (1).

Suppose first that A is B3. If

    a+b-c = d+e-f = x,

then the multiset equality {a,b,f}={d,e,c} follows. If x is outside A, c cannot belong to {a,b}, since otherwise x would be the other positive summand. Consequently c=f, and B2 then identifies {a,b} with {d,e}. Thus r(x) is at most one outside A. Together with h=1 on A, this proves Booleanity.

Conversely, suppose that two distinct triples T,U have the same sum. Their supports are disjoint: a common element could be cancelled, and B2 would identify the remaining pairs. Choose c in supp(T) and d in supp(U). Then

    x = sum(T)-c-d = sum(T\{c})-d = sum(U\{d})-c.

These are different signed-pair representations, since c != d. Also x is outside A: otherwise B2 applied to sum(T\{c})=x+d would place d in supp(T), a contradiction. Hence h(x)=r(x)>=2. This proves the converse. The support assertion follows from the definition of r. QED.

For comparison with a Fourier formulation, let f^[2](x) count the a in A satisfying 2a=x. B2 ensures this function is Boolean, even if doubling is not injective on the ambient group. Exactly

    g = (f*f + f^[2])/2,

and therefore

    h = ((f*f + f^[2]) * 1_(-A))/2 - (n-1)f.      (3)

The full pointwise Boolean requirement in (3) is not a relaxation: it is precisely B3, once B2 is known.

## 2. Weighted Boolean defects count actual triple collisions

Let C(A) be the collection of unordered pairs {T,U} of distinct multiset triples from A having the same sum. Let s(T) denote the number of distinct elements in T.

### Proposition 2

For every B2 set A, with h as above,

    sum_x binom(h(x),2)
      = sum_{{T,U} in C(A)} s(T)s(U).              (4)

In particular, if C_3(A)=|C(A)|, then

    C_3(A) <= sum_x binom(h(x),2) <= 9 C_3(A).     (5)

A collision between two triples with three distinct elements each has weight exactly nine, not one.

### Proof

Since h=1 on A, the left side counts unordered pairs of distinct signed-pair representations of a common x outside A. Write such a pair as

    x = sum(P)-c = sum(Q)-d,

where P,Q are multiset pairs. If c=d, B2 gives P=Q, so c != d. The triples

    T = P + {d},       U = Q + {c}

have equal sums. They cannot be equal as multisets: equality would put c in P, making x an element of A. Thus they are distinct, and their supports are disjoint by B2.

Conversely, given a collision {T,U}, choose one distinct element d in supp(T) and one c in supp(U), and form

    P = T\{d},        Q = U\{c},
    x = sum(T)-d-c.

As in Proposition 1, x is outside A, and the resulting signed representations are distinct. The constructions are inverse. Repeated copies of an element give only one choice of that element, explaining the support factors s(T)s(U). This proves (4), and 1<=s(T),s(U)<=3 proves (5). QED.

Example: A={0,1,3} is B2 but not B3. The collision {0,0,3} versus {1,1,1} has weight 2. Exactly h(-1)=h(2)=2, and the defect sum is 2.

### What this does not prove

Formula (4) does not bound the Boolean support by N, nor force its cyclic density to be at most one half. The mass identity (1) is unchanged for B2 sets which are not B3. Thus a proof that substitutes only the mass of h, or only a scalar moment consequence of Booleanity, has dropped precisely the collision information that (4) retains.

No new sign inequality involving joint translates of h was proved in this attack. In particular, no forest assumption, Fourier-flatness assumption, or unproved comparison between representation-graph overlaps and holes is made.

## 3. Cartesian B3 sets are exactly bipartite graphs of girth at least eight

Let X and Y be B3 sets in abelian groups, and let C be a subset of X x Y. Associate to C the simple bipartite graph G_C with vertex parts X,Y and edge xy for (x,y) in C.

### Proposition 3

C is B3 in the product group if and only if G_C has neither a 4-cycle nor a 6-cycle.

### Proof

A 4-cycle gives two different pairs of edges with equal coordinate sums. Padding both pairs by the same edge gives a collision between multiset triples. Padding is legitimate even if that edge occurs twice in a triple. A 6-cycle directly gives a collision between its two alternating triples of edges.

Conversely, suppose that two multiset triples of edges have the same sum. The B3 properties of X and Y identify the multisets of left endpoints and of right endpoints. Cancel any common edge occurrences, and color the remaining edges red and blue according to their originating triple. At every vertex the red and blue degrees are equal, counting multiplicity.

If any edges remain, orient red edges from left to right and blue edges from right to left. The resulting nonempty finite directed multigraph has equal indegree and outdegree at every vertex, so it contains a directed cycle. There are at most six edge occurrences in total. A directed 2-cycle would require the same graph edge in both colors, which cancellation excluded. The graph is bipartite. Taking a simple directed cycle therefore yields a 4-cycle or 6-cycle in G_C. This contradicts the hypothesis. QED.

For integer alphabets contained in [0,L], the encoding

    (x,y) -> x + R y,       R > 3L,

preserves and reflects equality of triple sums: the first-coordinate sum difference has absolute value at most 3L<R. Thus Proposition 3 also describes a literal carry-free integer construction.

The necessity of excluding 4- and 6-cycles does not require the alphabets themselves to be B3 or the radix to be carry-free. Alternating cycles have exactly matching endpoint multisets, so they give integer equalities under every additive positional encoding.

## 4. The precise size loss

### Proposition 4

If a bipartite graph has at most n vertices in each part and has no 4-cycle or 6-cycle, its number of edges m satisfies

    m <= n^(4/3) + 3n.                            (6)

Consequently the Cartesian construction in Proposition 3 has at most (1+o(1))n^(4/3) elements when |X|=|Y|=n.

### Self-contained proof

Delete vertices of degree zero or one until the graph is empty or has minimum degree at least two. At most 2n edges are deleted. Write m_0 for the remaining number of edges and u,v<=n for the remaining part sizes.

If m_0<=n, (6) is immediate. Otherwise define

    P = sum_{xy an edge} (deg(x)-1)(deg(y)-1).

This counts non-backtracking paths of length three, oriented from the left part to the right part. Such a path has nonadjacent endpoints, because otherwise there is a 4-cycle. Two different such paths with the same endpoints create a 4-cycle if they share an internal vertex, and a 6-cycle otherwise. Hence

    P <= uv-m_0 <= n^2.                           (7)

All remaining degrees are at least two. The function psi(t)=t log(t-1) is convex on [2,infinity), since

    psi''(t) = (t-2)/(t-1)^2 >= 0.

The arithmetic-geometric mean inequality over the edges, followed by Jensen separately on the two vertex parts, gives

    P/m_0
      >= exp((1/m_0) sum_x deg(x)log(deg(x)-1)
             +(1/m_0) sum_y deg(y)log(deg(y)-1))
      >= (m_0/u-1)(m_0/v-1)
      >= (m_0/n-1)^2.                             (8)

The last step uses m_0>n, so both comparison factors are positive. Put d=m_0/n>1. Equations (7)-(8) give

    d(d-1)^2 <= n.

Since d>=d-1, this implies d<=n^(1/3)+1. Thus m_0<=n^(4/3)+n, and restoring the at most 2n deleted edges proves (6). QED.

### The exponent 4/3 is sharp for two blocks

For each prime power q, take the one-dimensional subspaces of F_q^4 as points, and the two-dimensional totally isotropic subspaces for a nondegenerate alternating form as lines. Both part sizes are

    n = q^3+q^2+q+1.

Indeed each point lies on q+1 such lines: these lines correspond to the one-dimensional subspaces of the two-dimensional quotient p^perp/p. Each line contains q+1 points, so incidence counting gives the same number n of lines. The incidence graph has m=(q+1)n edges.

Two distinct points determine at most one line, excluding a 4-cycle. A 6-cycle would give three distinct points pairwise orthogonal and three different joining lines. If the points were independent, they would span a three-dimensional totally isotropic space, impossible because W subset W^perp implies dim(W)<=2 in a nondegenerate four-dimensional space. If dependent, their joining lines would coincide. Thus there is no 6-cycle either.

Labeling the two vertex parts by any two n-element B3 alphabets therefore gives a B3 subset of their product with

    m=(q+1)n=(1+o(1))n^(4/3).

This proves sharpness of the two-block exponent, not achievability of rate 2/3 for arbitrary-length codes over a fixed alphabet.

## 5. Consequence for asymptotic additive-code amplification

A code C subset [n]^k is called coordinatewise 3-multiset-separable here if equality of the coordinatewise multisets for two triples of codewords forces equality of the triples as multisets of codewords. Repeated codewords are included.

Split the k coordinates into two blocks. Each codeword becomes an edge between its two block words. A 4-cycle or a 6-cycle gives matching multisets of entire block words on both sides, hence matching multisets in every individual coordinate. It is therefore forbidden for every such code, regardless of any additional constraints within the blocks.

For even k=2l, the two parts have at most n^l vertices each. Proposition 4 gives

    |C| <= n^(2k/3) + 3 n^(k/2).                 (9)

For odd k, using parts of size at most n^ceil(k/2) gives the same asymptotic rate bound. For fixed n>=2,

    limsup_{k->infinity} log_n(|C|)/k <= 2/3.      (10)

In particular, a scheme that would amplify a finite B3 advantage by retaining n^(k-o(k)) words from a Cartesian k-th power is impossible.

For an integer base alphabet A of size n in [0,L], any injective additive positional encoding of a subset of A^k must satisfy (9) if its image is B3: alternating cycles remain exact sum equalities even in the presence of carries. For fixed even k, if L is of order n^3 and the radix is of order L, the upper bound in (9) is of order n^(2k/3), while the cube-root scale of the natural full positional ambient interval is of order n^k. At that ambient scale, the literal product-and-restriction strategy loses a power of n, not merely a constant.

This does not exclude nonlinear or interacting-coordinate constructions, or a separate method which drastically reduces the diameter of the selected code's integer image. It supplies no upper bound of the desired strength for arbitrary B3 subsets of [1,N].

## 6. Exact verification

Run:

    python3 Submission/independent_b3_audit.py

It writes `Submission/independent_b3_audit.json` and independently checks:

- Propositions 1-2 for every B2 subset of {0,...,12}: 668 sets, of which 314 are B3 and 354 have positive Boolean defect.
- The same formulas for all B2 subsets of each cyclic group of order 3 through 13, including groups with 2- and 3-torsion.
- Proposition 3 by two separate tests (enumerated repeated integer triple sums, and forbidden cycle masks) for all 512 subgraphs of K_{3,3} and all 65,536 subgraphs of K_{4,4}. The respective maximum edge counts are 5 and 8.
- The symplectic constructions for q=2 and q=3: 45 edges on two parts of size 15, and 160 edges on two parts of size 40. It checks the absence of both short even cycles and directly enumerates, respectively, 16,215 and 695,520 repeated integer triples in the encoded sets.

These are audits of the stated finite identities and constructions. They are not experimental evidence asserted to settle the original asymptotic.

## 7. Remaining gap

A decisive proof still requires a genuinely stronger global constraint on arbitrary B3 sets: either an interval-specific inequality forcing n^3 <= (1+o(1))N, or a construction with a fixed cubic excess for unbounded n. Neither Proposition 2's exact Boolean defect formula nor Proposition 4's Cartesian obstruction supplies that missing constraint. The supplied conditional Lean reduction remains conditional.
