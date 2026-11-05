# A collision-aware counterexample to the universal anchor-gauge inequality

## Conclusion

The proposed universal inequality

\[
2^{1-\binom{n-1}{2}}e_n(\chi)
\leq 2^{\binom n2/2}\sqrt{p_{n+1}(\chi)}
\tag{AG}
\]

is **false in the intended asymptotic range**. A counterexample occurs at
`n = 32`, on arbitrarily large vertex sets. In fact, for every integer `t >= 2`
there is a two-colouring `chi` on `32t` vertices satisfying

\[
e_{32}(\chi)\geq D:=\frac{32!}{32^{32}}>2^{-43},
\qquad p_{33}(\chi)\leq 2^{-1536}.
\tag{1}
\]

Here densities are over actual vertex subsets, with distinct vertices. Block
labels need not be distinct, and all repeated-label contributions are included.
Thus this is not an argument that discards collisions in a finite clique-free
example.

The same construction disproves every weakening of (AG) whose squared gauge
cost is `O(n^2)`. It does not disprove the minimum-density recurrence itself,
and does not settle the fixed natural-coefficient proposition `P`.

## 1. The gauge identity is correct

All colours and coboundaries below are in `F_2`. For a pair-colouring `G`, put

\[
(\delta G)(abc)=G(ab)+G(ac)+G(bc).
\]

A triple-colouring on an `n`-set is *cocyclic* if its four-face sums vanish on
all four-subsets. This is equivalent to being `delta F` on that set:
choose an anchor `v`, set `F(vi)=0` and `F(ij)=chi(vij)`, and use the parity
identity on `vijk`.

The kernel of the pair-to-triple coboundary consists exactly of cuts
`G(ij)=u_i+u_j`, and has size `2^(n-1)`. Consequently the image has size
`2^choose(n-1,2)`. Both constant triple-colourings are in the image, since the
coboundary of the all-one pair-colouring is the all-one triple-colouring.

If `chi` is cocyclic on the set, exactly `2 * 2^(n-1)` pair-colourings make
`chi + delta G` monochromatic. If it is not cocyclic, none do. Averaging over
vertex subsets gives the exact finite identity

\[
\mathbb E_G p_n(\chi+\delta G)
=2^{1-\binom{n-1}{2}}e_n(\chi).
\tag{2}
\]

Squaring (AG), which has nonnegative sides, gives its equivalent form

\[
p_{n+1}(\chi)\geq
2^{-\{\binom n2+2\binom{n-1}{2}-2\}}e_n(\chi)^2
=2^{-n(3n-7)/2}e_n(\chi)^2.
\tag{3}
\]

The false step is (AG)/(3), not (2).

## 2. A cocyclic base with no monochromatic nine-set

There exists a graph pair-colouring `F` on 32 labels such that

\[
\psi(ijk):=F(ij)+F(ik)+F(jk)
\]

has no monochromatic nine-set.

A short probabilistic proof suffices. On a specified `s`-set, `delta F` is
constant precisely when `F` is a cut or a complement of a cut. There are
`2^s` such graphs out of `2^choose(s,2)`. Thus for a uniform random `F`, the
expected number of monochromatic nine-sets of `delta F` is

\[
\binom{32}{9}2^{9-\binom92}
=\frac{28048800}{2^{27}}
=\frac{876525}{4194304}<1.
\]

Hence some `F` has none. The verifier accompanying this note also contains an
explicit 32-vertex adjacency matrix. It exhaustively certifies 11 monochromatic
`delta F` eight-sets and zero monochromatic nine-sets. Independently,
`delta^2 F=0` proves that the base is cocyclic on every subset.

## 3. Blow up the base and randomize the collisions

Partition `32t` actual vertices into 32 classes of equal size `t`. Colour a
triple as follows:

* If its three block labels are distinct, use the deterministic colour
  `psi` of those labels.
* If a block label repeats, give this actual triple an independent fair bit.

The independent bits are assigned **per actual triple**, not per multiset of
block labels. This distinction is essential to the argument.

### Cocyclic 32-sets

Every 32-set containing one vertex from each block is cocyclic. All of its
triple colours come from `delta F`, and all four-face parities vanish. There
are exactly `t^32` such sets. For every realization of the random bits,

\[
e_{32}(\chi)\geq \frac{t^{32}}{\binom{32t}{32}}
\geq\frac{32!}{32^{32}}=D.
\tag{4}
\]

The second inequality uses `binom(32t,32) <= (32t)^32/32!`, so no limiting
approximation or vertex-collision omission is involved.

### Monochromatic 33-sets

A monochromatic 33-set cannot meet nine or more blocks: choosing one vertex
from each of nine occupied blocks would give a monochromatic nine-set of
`psi`.

Suppose it meets at most eight blocks, with occupancies `a_1,...,a_8`, padded
by zeros, where `sum a_i = 33`. Its deterministic triples number

\[
\sum_{i<j<k}a_i a_j a_k.
\]

This sum is maximized by balancing the occupancies. Indeed, transferring one
unit from `a_i` to `a_j` when `a_i >= a_j+2` changes the sum by

\[
(a_i-a_j-1)\sum_{h\ne i,j}a_h\geq0.
\]

Consequently its maximum occurs at `(5,4,4,4,4,4,4,4)`, and equals

\[
\binom73 4^3+\binom72 5\cdot4^2=2240+1680=3920.
\]

Every such 33-set therefore has at least

\[
\binom{33}{3}-3920=5456-3920=1536
\tag{5}
\]

independently randomized triples.

If it occupies at least three blocks, its deterministic triples either have
inconsistent colours, giving monochromatic probability zero, or specify a
unique possible monochromatic colour. In the latter case all randomized
triples must equal that colour, with probability at most `2^-1536`.

If it occupies at most two blocks, all 5456 triples are randomized and its
monochromatic probability is `2^(1-5456)`, which is smaller still.

Averaging over all actual 33-subsets gives

\[
\mathbb E p_{33}(\chi)\leq2^{-1536}.
\tag{6}
\]

For every `t >= 2`, some realization has `p_33 <= 2^-1536`, while (4) holds
for every realization. This proves (1) on arbitrarily large vertex sets.

## 4. Exact contradiction at n = 32

At this index,

\[
\binom{31}{2}=465,\qquad\binom{32}{2}=496,\qquad
\frac{32(3\cdot32-7)}2=1424.
\]

Also `32! > 2^117`, so `D > 2^-43`. For the colourings just constructed,

\[
2^{1-\binom{31}{2}}e_{32}(\chi)
\geq2^{-464}D>2^{-507},
\]

whereas

\[
2^{\binom{32}{2}/2}\sqrt{p_{33}(\chi)}
\leq2^{248}2^{-768}=2^{-520}.
\]

This contradicts (AG) by a factor greater than `2^13`. Equivalently, the
required lower bound in (3) exceeds `2^-1510`, while the actual density is at
most `2^-1536`.

Using the exact factorial, rather than the convenient integer-power bound,
the guaranteed squared gap is

\[
1536-1424+2\log_2 D=27.3265273047\ldots
\]

bits. A putative weakened inequality

\[
2^{1-\binom{31}{2}}e_{32}(\chi)
\leq2^{K(32)/2}\sqrt{p_{33}(\chi)}
\]

would already require

\[
K(32)\geq1536-928+2\log_2D
=523.3265273047\ldots,
\]

instead of the proposed `K(32)=496`. Thus an extra factor two in the squared
cost does not repair this example.

## 5. Why every quadratic-cost version fails

For large `n`, use `n` equal blocks and choose a base graph with no
monochromatic `delta F` set of size `s=2*ceil(log_2 n)+1`. Write
`ell=ceil(log_2 n)`, `k=2ell`, and `s=k+1`. The first-moment bound is

\[
\binom ns 2^{s-\binom s2}
\leq \frac{n^s}{s!}2^{s(1-\ell)}
\leq\frac{2^s}{s!}<1.
\]

The same construction then satisfies, on arbitrarily large vertex sets,

\[
e_n\geq D_n:=n!/n^n,\qquad
p_{n+1}\leq2^{-L_n},
\]

where, putting `m=n+1`,

\[
L_n=\binom m3-
\max_{a_1+\cdots+a_k=m}\sum_{i<j<h}a_i a_j a_h.
\]

The maximum again has balanced integer occupancies. Equivalently,
Maclaurin's inequality gives the useful lower bound

\[
L_n\geq\frac{m^3}{2k}-\frac{m^3}{3k^2}
-\frac{m^2}{2}+\frac m3.
\]

In particular,

\[
L_n=(1+o(1))\frac{n^3}{4\log_2 n}.
\]

Any universal inequality with squared gauge cost `K(n)`,

\[
2^{1-\binom{n-1}{2}}e_n
\leq2^{K(n)/2}\sqrt{p_{n+1}},
\]

must satisfy

\[
K(n)\geq L_n+2-2\binom{n-1}{2}+2\log_2D_n
=(1+o(1))\frac{n^3}{4\log_2 n}.
\tag{7}
\]

Thus no `O(n^2)` squared cost can be universal. The obstruction is precisely
that a locally cocyclic transversal core need not control noisy repeated-label
completions.

### Scope of the conclusion

* The exact gauge identity survives unchanged.
* The displayed universal asymptotic inequality is genuinely refuted for
  `n >= 4`; it fails at `n=32`, and quadratic-cost versions fail at arbitrarily
  large indices.
* This does **not** refute a statement restricted to density-minimizing
  colourings. Nor does it refute an inequality between the constants `c_n`
  themselves: the constructed colourings are not asserted to minimize
  `p_(n+1)`.
* Equation (7) is a necessary cost, not a proof of a valid higher-cost bound.
  A higher-order tail cost could in principle still fit a weighted recurrence
  budget. No such adequately costed positive inequality is established here.
* No disproof of the fixed natural-coefficient proposition `P` follows from
  this counterexample. `Spec.lean` and every pre-existing helper are unchanged.

## Verification

Run from the repository root:

```text
python Submission/verify_anchor_gauge.py
```

The standard-library-only script checks the explicit base graph, all 3828
sorted padded occupancy patterns for 33 vertices in at most eight blocks, the
exact rational contradiction, and the gauge identity exhaustively on three,
four, and five vertices. Floating-point logarithms are used only to report
the gap in bits, not to certify any inequality.
