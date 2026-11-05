# Unimodular auxiliary factors and the pointwise Erdős–Straus gap

**Scope.** All theorem names below are checked in the sorry-free
`Submission/AdjacentFactor.lean`, which does **not** import or edit
`Submission/Spec.lean`. The results provide an exact, finite test for a
**restricted** Type-I family, a sharp factor-index bound, and a Type-II
congruence duality. They neither prove the conjecture nor exhibit a prime
counterexample. `Good(p)` requires three *strictly increasing* positive
integer denominators.

## Consecutive auxiliary offsets

For `p=24k+1` and `i≥0`, set

    h_i=4i+3,    M_i=((4i+3)p+1)/4=(4i+3)(6k)+i+1.

The quotient is exact. For **every** `k,i,j` (without assuming primality),

    M_{i+1}=M_i+p,        h_j M_i+i=h_i M_j+j.             (1)

In particular `h_{i+1}M_i=h_i M_{i+1}+1`, so consecutive `M_i` are
coprime; more generally, `gcd(M_i,M_j) | (j−i)` when `i≤j`. Lean proves
`auxiliaryFactor_identity`, `auxiliaryFactor_increment`,
`auxiliaryFactor_det`, `auxiliaryFactor_coprime`, and
`auxiliaryFactor_gcd_dvd_gap`. Coprimality in (1) alone does **not**
force any factor into a desired residue class.

## A finite and sharply bounded *restricted* Type-I factor test

**Theorem (`simple_typeI_iff_auxiliary_divisor`).** For every `k≥0`, the
following statements are equivalent:

1. There are `p/4<x<p/2` and `c>0` such that **`c|x`** and, with
   `a=4x−p`, **`a|4c+1`**.
2. There are `i,q` with `7i+3≤6k`, `q>1`, `q|M_i`, and
   `q≡−1 (mod h_i)`.

The first statement implies a Type-I certificate `c|x²` and an ordered
solution, but it imposes the *extra* requirement `c|x`. The original
Type-I criterion only asks `c|x²`; moreover Type II can succeed when
Type I does not. **This equivalence is NOT an equivalence for `Good(p)`.**
The index `i` is an auxiliary-factor index, *not* the original candidate
first-denominator index `j`.

Here is the exact algebra in both directions. From (2), write

    h=h_i,    c=M_i/q,    t=(q+1)/h,    x=tc.

Then `h p+1=4qc`, `q+1=ht`, and

    h(4x−p)=4c+1,
    4/p=1/(tc)+1/(qtc)+1/(pqc),    tc<qtc<pqc.              (2)

The last inequalities and fraction identity are Lean-proved; no
primality assumption is needed for this conditional construction.
Conversely, write `x=tc` in (1), set
`h=(4c+1)/a` and `q=ht−1`. As `p≡1 (mod 4)`, both `a` and `h` are
`3 (mod 4)` (and `h≥3`); direct expansion gives `hp+1=4qc`.
Therefore `h=4i+3`, `q|M_i`, and `q≡−1 (mod h)`. This *reverse*
translation is proved as `simple_typeI_factor_product`, complementing
the construction in `FactorTrisection.lean`.

**Uniform index restriction (`factor_product_index_sharp` and
`auxiliary_divisor_index_sharp`).** Every eligible factor in (2), not
just a selected minimal one, obeys

    7i+3 ≤ 6k.                                                 (3)

Indeed `a h=4c+1`, `4x=p+a` and `c≤x` yield
`(h−1)a≤p+1=24k+2`. If `a≥7`, substitute `h=4i+3` to get
`7(4i+2)≤24k+2`, exactly (3). If `a=3`, then `x=6k+1` is odd;
`t=x/c` cannot be `1`, since `c=x` would give
`3|4x+1=24k+5`, and cannot be `2`, since `x` is odd. Therefore
`t≥3`. The equation `3(4i+3)=4c+1` gives `c=3i+2`, so
`6k+1=x=tc≥3c=9i+6`, which is stronger than (3).
The cutoff is **pointwise** but grows with `p`; it does *not* provide
an eligible factor for every prime. Its length is reminiscent of the
sharp `7j<6k` Type-II first-denominator bound in
`HardTypeIISize.lean`, but the two indices refer to different objects.

**Sharpness at infinitely many hard primes.** For every `n≥0` take

    p=168n+97,  k=7n+4,   i=6n+3,
    h=24n+15,  q=h−1=24n+14,  c=x=42n+26.

Then `7i+3=6k`, `q|M_i`, `q≡−1 (mod h)`, `a=4x−p=7`, and
`4c+1=7h`. The identity (2) is strictly ordered. Since
`gcd(97,168)=1`, Dirichlet's theorem gives infinitely many *prime*
values in this progression. `auxiliary_sharp_family` and
`infinitely_many_sharp_auxiliary` verify the family, the bound's equality,
and prime existence in Lean. The first prime is `p=97`, with
`4/97=1/26+1/364+1/35308`. This shows (3) cannot be tightened
uniformly even for primes; it says nothing about arbitrary other primes.

The restriction **`c|x` must not be silently removed**. For instance,
`p=73`, `x=20`, `a=7`, `c=40` satisfy `40|20²`, `7|4·40+1`, but
`40∤20`. The resulting `h=(4c+1)/a=23=4·5+3`, `k=3`, and
`7·5+3=38>6k=18`: even the bound (3) fails for this legitimate
*general* Type-I certificate.

## Why adjacent coprimality does not force the target divisor

The hard prime `p=2521=24·105+1` provides a certified warning. Its
first three auxiliary factors are

    M_0=1891=31·61,         h_0=3;    all divisor residues are 1,
    M_1=4412=2²·1103,       h_1=7;    divisor residues are {1,2,4},
    M_2=6933=3·2311,        h_2=11;   divisor residues are {1,3}.

In each row there is **no divisor `q≡−1 (mod h_i)`**, even though
adjacent `M_i` are coprime by (1). `auxiliary_2521_first_three_miss`
checks *every* positive divisor in each row in Lean. At the **next**
index, `M_3=9454=2·29·163`, `h_3=15` and `29≡14 (mod 15)`;
(2) gives `x=652,c=326` and the already-known ordered identity

    4/2521 = 1/652 + 1/18908 + 1/23833534.

`auxiliary_2521_fourth_works` verifies the eligible divisor and `Good
2521`. This finite example disproves a *proposed short-neighbor
forcing step*, not the original conjecture or an unbounded factor test.

## Exact duality for the full Type-II modular parameters

For **arbitrary** `p,m` with `m>0` and `d|m²`, set `h=4m−1` and
`e=m²/d`. The Lean theorem `typeII_modular_dual` proves the two-sided
equivalence

    h | p+4d     ↔     h | 4pe+1.                              (4)

Indeed `de=m²`, `16m²=h(4m+1)+1`, and hence

    4e(p+4d)=(4pe+1)+h(4m+1).

Furthermore `gcd(h,4e)=1`: `h+1=4m` makes `h` coprime to both `4`
and `m`, and `e|m²`. Thus the factor `4e` can be cancelled in *both*
directions. Neither divisibility condition in (4) is guaranteed to
hold for a chosen hard prime. For example, with
`(p,m,d,e,h)=(2521,22,44,11,87)`, both `87|2521+176` and
`87|4·2521·11+1` hold; this is one existing witness in two forms,
not two independently forced witnesses.

## Verification and remaining pointwise gap

`lake env lean Submission/AdjacentFactor.lean` and
`lake build Submission.AdjacentFactor` succeed. Auditing the principal
new declarations with `#print axioms` shows only Lean's ordinary
`propext`, `Classical.choice` and `Quot.sound`; no `sorryAx`, added
axiom, or import of `Spec.lean`. Independent exact fraction and divisor
checks validate the displayed examples, but no finite check is used to
assert a universal theorem.

What remains unproved is **for every prime `p=24k+1`, find some
`j<6k`** for which either `c|x_j²` and `4j+3|4c+1`, or
`0<d<x_j`, `d|x_j²` and `4j+3|x_j+d`, where
`x_j=6k+1+j`. In particular, proving that an eligible `q|M_i`
exists for every hard prime would be a *stronger* all-prime statement
than the conjecture, not a consequence of (1)–(4). To disprove the
conjecture instead requires a *certified hard prime* failing both full
conditions for **every** `j`; the `2521` fiber test does nothing of
the sort. The exact equivalence with the original ordered conjecture
is already Lean-proved in `CoveringGap.all_good_iff_explicit_hard_cover`.
