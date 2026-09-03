# Independent global continuation — unresolved

**No proof or disproof of `R(Q_d) <= C 2^d` was obtained.** No absolute
Ramsey constant or improved upper bound is claimed. The target throughout
was an ordinary injective monochromatic copy in an arbitrary two-colouring
of `K_N`, with `N=C2^d` and an absolute integer `C`. Neither admitted theorem
was used; no Lean file was edited.

## A checked obstruction to the separator-only halving attempt

One possible dimension-halving strategy is to delete a small source boundary,
embed the resulting independent pieces at dimension `k=floor(d/2)`, and then
restore the boundary. Small balanced separators of the cube do **not** give
the small pieces needed for this strategy at a vanishing deletion cost.

Precisely, let `d>=1`, `0<=k<d`, `h=2^d`, and `S subset V(Q_d)`. If every
component of `Q_d-S` has at most `2^k` vertices, then

\[
                 |S|\ge \frac{d-k}{2d-k}\,h.                 \tag{1}
\]

In particular, `k=floor(d/2)` requires `|S|>=h/3`.

**Proof.** For any nonempty cube vertex set `A`,

\[
                 2e(Q_d[A])\le |A|\log_2|A|.                 \tag{2}
\]

Here is an elementary proof of the input (2). Split `A` along one coordinate
into sizes `a,b`. The crossing edges form a matching, so induction bounds
twice its induced edge count by
`a log_2 a + b log_2 b + 2 min(a,b)`, with `0 log_2 0=0`.
This is at most `(a+b) log_2(a+b)`: the difference between the logarithmic
terms is `(a+b) H_2(a/(a+b))`, and binary entropy satisfies
`H_2(t)>=2 min(t,1-t)` by concavity on each half of `[0,1]`.
The dimension-zero base case is immediate.

Let `A_i` be the components of `Q_d-S`. By (2), their internal average
degrees are at most `k`, and hence

\[
 e(A_i,S)=d|A_i|-2e(Q_d[A_i])\ge(d-k)|A_i|.
\]

There are no edges between distinct components. Summing these inequalities
and using `e(V(Q_d)\setminus S,S)<=d|S|` gives
`(d-k)(h-|S|)<=d|S|`, which is (1). QED.

**Scope.** This rules out disconnecting the source into pieces of size at
most `2^k` by deleting `o(h)` vertices when `k=floor(d/2)`. It does not rule
out a dimension-halving Ramsey recurrence, a method that retains or reuses
the boundary, or any method that keeps cross-piece constraints. In particular,
a source deletion count is not automatically a lower bound on host overhead.

## Precise remaining gap

I did not find a two-colour lifting argument that simultaneously retains all
cross-piece cube edges, their common coordinate labels, and distinct original
host vertices. In the higher-block notation, a free block adjacent to fixed
blocks must use the coordinate-dependent domains

\[
 L_a=(V(G)\setminus U)\cap
          \bigcap_{y\text{ fixed neighbour}}N_G(F_y(a)).
\]

Within the recorded deletion budget, deleting used vertices preserves the
hypotheses of the capacity lemma; imposing these overlapping neighbourhood
constraints does not.
Neither positivity of the resulting constrained block partition nor a global
rebuild preserving the other constraints was proved here. I also did not
prove that failure of such a rebuild forces a cube in the opposite colour.
That is the missing global implication, not an injectivity convention or an
entropy calculation.

For example, the actual Ramsey recurrence

\[
 R(Q_d)\le 2^{d-k}R(Q_k)+A\,2^d/d,
 \qquad k=\lfloor d/2\rfloor,
\]

for `d>=2` with an absolute `A>=0`, **remains unproved**. Its normalized errors
would sum to at most `A` along a halving chain stopped at dimension one, but
neither (1) nor the available block estimates establishes this recurrence.
No local patch success probabilities were multiplied over overlapping patches.

## Audit

* The proof of (1) was checked separately by counting all edges leaving the
  components; its use of `d`, rather than `k`, in the upper bound `d|S|` is
  essential.
* Exhaustive enumeration of all 65,812 source subsets in dimensions `1..4`
  checked (2) using the exact integer inequality
  `2^(2e(A)) <= |A|^|A|`, and checked (1) for every admissible `k` using
  `(2d-k)|S| >= (d-k)2^d`. These finite checks only audit the displayed
  obstruction, not the Ramsey conjecture.
* The unchanged SHA-256 of `Submission/Spec.lean` is
  `9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b`.

**Conclusion:** the conjecture remains unresolved by this continuation.
