# Affine parabola targets: completed construction ceiling

All three modules below compile without admissions. Principal theorem audits use
only `propext`, `Classical.choice`, and `Quot.sound`.

## QuadraticBandPacking

`ordered_width_sum` charges increasing interval widths to the preceding gaps.
`band_width`, `band_charge`, and `branch_card` apply this to quadratic bands with
period p² and height A p. On a monotone branch of length p, assuming A>0,
2 A≤p and p≤Q², the integer points number at most the occupied-band count plus
Q+2 A. No distribution or primality assertion is used.

## AffineParabolaLevelBound

`short_slope` uses rational approximation to write h L=p j+d with
0<h≤Q and |d|≤Q when p≤Q². This turns

    floor(b²/p)+L b ≡ C (mod p)

into quadratic bands. Splitting at the vertex and bounding the occupied keys
proves `uniform_level_card` (at most 20 Q points when 2 Q≤p), then
`level_card_sq`: for any positive natural modulus p and integer L,C, a set S of
integer labels in [0,p] obeying this congruence satisfies |S|²≤1600 p.

## AffineParabolaHeightBound

Let f choose natural roots, with labels B⊆{1,...,p-1}, f(b)%p=b,
f(b)≤N, and a fixed target

    floor(f(b)²/p) ≡ lam*b+μ (mod p).

`height_square_bound`: |B|²≤1600 p (floor(N/p)+1)², by partitioning according
to f(b)/p and applying the preceding level theorem.

`small_height_card`: if N<p and IsCoprime (p:ℤ) lam, then
|B|≤floor(N²/p)+1. In this range f(b)=b and the square quotient is injective.

`affine_height_card_ceiling`: for unit lam and nonzero labels,

    |B|³≤6400 N².

The proof splits at p=N and p=N². Neither primality nor Sidonness is assumed;
the conclusion is specific to this modular root-representative mechanism.
The unsigned theorem requires f(b)%p=b. The additional theorem
`signed_affine_height_card_ceiling` allows f(b)%p=b OR f(b)%p=p-b
independently at each label, with the same carry target. It proves

    |B|³≤51200 N².

The proof partitions the labels by residue sign and reindexes the negative
class using b↦p-b; its target slope becomes -lam, still a unit. It combines
the two unsigned estimates using (x+y)³≤4(x³+y³). All four principal height
module audits are now clean. This extension still concerns a fixed affine
target, not arbitrary square Sidon sets.

This does not settle Erdős 773: arbitrary square Sidon subsets need not satisfy
one fixed affine target. Spec.lean is unchanged and retains its unresolved
0<ε<1/3 branch.

Logs: /tmp/quadratic-band-packing.log, /tmp/affine-parabola-level.log,
/tmp/affine-parabola-height.log.
