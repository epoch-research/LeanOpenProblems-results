# Augmentation continuation: no settlement

`Spec.lean` was not modified in this continuation. It still has its sole
admission for 0 < epsilon <= 1/3. No proof submission has been made.

## What the elementary blocking count supplies

For a Sidon root set S, a new root x can be blocked in either of these forms:

    2*x^2 = a^2+b^2,
    x^2+a^2 = b^2+c^2,

where a,b,c belong to S. These are precisely the two kinds of condition in
`Set.IsSidon.insert`, applied to the set of squares.

In the second form x not in S implies a != b. Fixing a,b therefore fixes a
nonzero square difference, and the existing divisor estimate bounds the
number of pairs (x,c). This elementary counting route bounds blocked roots
by O(|S|^2 D), where D bounds the positive square-difference multiplicities.
The first form adds at most |S|^2 possibilities. Inclusion-maximality thus
supplies only a square-root-scale lower bound (up to the D loss), weaker
than the already proved alteration bound.

Crucially, this count does not bound the number of *old roots to remove*
when adding a collection of outside roots. A single outside root can have
many different blocking triples. Bounded difference multiplicity does not
provide a common small hitting set for those triples. No profitable-exchange
lemma giving a better exponent was obtained. These observations are an
analysis of the proposed route, not a new Lean theorem or an upper bound on
the actual maximum.

## Ordered normalization

The existing verified lemma `ordered_square_collision_parameters` gives
positive z,y,k and

    b = a+z+k,
    c = a+z+k+y,
    d = a+2*z+k+y,
    k*(2*a+k) = 2*z*(z+y).

Reducing the last equation modulo 2 shows k is even. Writing k=2*t gives

    2*t*(a+t) = z*(z+y).

The factor 2 on the left must be retained. This normalization has not
produced the missing exchange estimate, and was not added to the main file.
Three-root obstructions must also be handled separately; the ordered lemma
assumes four distinct roots.

## Other directions reconsidered

No new construction or upper bound was obtained from rational-rotation
coloring, multiscale digit lifting, or small-prime residue profiles. In
particular, one cannot replace the missing integrality argument by the
near-linear fractional-capacity theorem.

The next advance still needs to yield N^(1-o(1)) actual Sidon roots, or a
fixed positive exponent loss on an unbounded sequence. The existing
subpower-loss upper bounds are compatible with the original conjecture.
