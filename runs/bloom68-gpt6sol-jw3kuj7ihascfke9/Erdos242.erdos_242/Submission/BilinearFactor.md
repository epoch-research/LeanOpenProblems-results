# A sharp bilinear lattice for **restricted** Type-I certificates

**Status.** `BilinearFactor.lean` and `SquareFactorObstruction.lean` are sorry-free Lean developments. Neither proves the Erdős–Straus conjecture nor finds a bad prime. `Spec.lean` is not imported or edited. The restriction **`c ∣ x`**, instead of the original `c ∣ x²`, is essential throughout the lattice equivalence and all its sharp bounds.

## Parameter-preserving correspondence

Set `p=24k+1`, `N=6k+1`, `x=N+j`, `a=4x−p=4j+3`. For an auxiliary index `i` put

    h=4i+3,     M_i=6kh+i+1=(hp+1)/4.

The Lean theorem `simple_typeI_iff_bilinear` establishes, for every `k` (without assuming primality), the exact equivalence

    ∃ x,c>0 : c∣x, p<4x, 2x<p, (4x−p)∣4c+1
      ⇔  ∃ i,j,t≥0 : t>0, N=(3i+2)t+((4i+3)t−1)j.       (1)

From a specified bilinear point, define

    q=ht−1,    c=hj+3i+2,    x=tc=N+j.

Then `q>1`, `j<6k`, `h a=4c+1`, `hp+1=4qc`, and `q∣M_i` with `q≡−1 (mod h)`. Conversely, **the same** eligible factor `q` determines `c=M_i/q`, `t=(q+1)/h`, and the bilinear point with that same `i,q,c,t` (`factor_product_of_auxiliary_divisor`, `bilinear_of_factor_product`). A specified original simple-Type-I cofactor `c∣x` likewise recovers the bilinear point (`bilinear_of_simple_typeI`). Thus these translations do not quietly replace an arbitrary factor by a more favorable one. The strictly ordered unit-fraction identity from any point is

    4/p = 1/(tc) + 1/(qtc) + 1/(pqc),     tc<qtc<pqc.    (2)

These constructions work conditionally for composite `p` too. **Equation (1) is not equivalent to general Type I, Type II, `Good(p)`, or the conjecture.** The auxiliary index `i` is different from the candidate-denominator index `j`.

## Bounds applying to *every* such point

`bilinear_cofactor_at_least_five`, `bilinear_index_sharp_direct`, `bilinear_parameter_bounds`, `bilinear_first_index_sharp`, and `bilinear_auxiliary_divisor_sharp` prove

    c≥5,                         7i+3≤6k,
    (3i+2)t≤N,                   5t≤6k+2,
    i>0 ⇒ 5t≤N,                5j+3≤6k,
    5(q+1)≤7N.                                                (3)

In particular, `10x≤3p+1` (`simple_typeI_first_denominator_sharp`); the restricted construction's first denominator lies below approximately `0.3p`, **not** merely below `p/2`. The final bound applies to **each specified eligible `q∣M_i`**, by `auxiliary_divisor_size_sharp`; its factor index satisfies the previous sharp bound in `AdjacentFactor.lean`. These are sound finite pruning rules but give no factor existence.

The equality cases in (3) are rigid and genuinely optimal even among arbitrarily large hard **primes**:

| Bound | Equality parameters | Arithmetic progression and example |
|---|---|---|
| `5j+3≤6k` / `10x≤3p+1` | exactly `i=0,t=2` | `p=120n+73`, `k=5n+3`, `j=6n+3`, `c=18n+11`, `x=36n+22`; for `p=73`, `x=22` |
| `5t≤6k+2` | exactly `i=0,j=1` | same `p=120n+73`, `t=6n+4`, `c=5`, `x=30n+20`; for `p=73`, `x=20` |
| `5(q+1)≤7N` | attained at `i=1,j=0` | `p=120n+97`, `k=5n+4`, `t=6n+5`, `c=5`, `q=42n+34`; for `p=97`, `q=34` |
| `7i+3≤6k` (also `AdjacentFactor.lean`) | attained at `i=6n+3,j=1,t=1` | `p=168n+97`, `k=7n+4`; for `p=97`, `i=3` |

`bilinear_first_equality_iff`, `bilinear_shift_equality_iff` prove the first two “exactly” statements. Their equalities force `p≡73 (mod 120)`; at `p=73` the *two distinct* ordered first denominators are `22` and `20`. Explicit family theorems certify each row. Dirichlet's theorem (used by the four `infinitely_many_…_sharp` declarations and by `infinitely_many_sharp_auxiliary` in `AdjacentFactor.lean`) proves that the relevant progressions contain arbitrarily large primes. It proves nothing for primes in other progressions.

The restriction `c∣x` cannot be dropped: `p=97,x=34,c=68` satisfy `c∣x²` and `39=4x−p∣4c+1=273`, but `c∤x` and `10x=340>3p+1=292`. Similarly `p=73,x=20,c=40` is a **general** Type-I certificate (`7∣161`, `40∣20²`) whose corresponding `h=23` would violate the restricted auxiliary-index bound. No bound from (3) is claimed for every full Type-I witness.

## Additional auxiliary reciprocity, and why it still falls short

`SquareFactorObstruction.lean` proves that **every** eligible auxiliary divisor `q` (even or composite) satisfies

    Jacobi(q,24k+1)=−1,

so `q` is nonsquare modulo `24k+1`; this requires neither primality of the numerator nor of `q`. The proof uses `q≡−1 (mod 4i+3)`, quadratic reciprocity on the odd part of `q`, and `M_i≡i+1 (mod 2)` to deal with powers of two. This is a **necessary sign**, not the exact factor congruence: knowing that an arbitrary nonresidue exists does not give `q∣M_i` with `q≡−1 (mod h)`. The same file rules out the restricted lattice when `24k+1` is a square, and supplies arbitrarily large such *composite* examples. The stronger theorem in `PointwiseJacobi.lean` rules out **all** Type-I predicates for **every** square numerator, not Type II; see `PointwiseJacobi.md`.

The missing conjectural step is unchanged: for each **prime** `p=24k+1`, find some `j<6k` with `x=6k+1+j`, `a=4j+3` and **either** `c>0, c∣x², a∣4c+1` **or** `0<d<x, d∣x², a∣x+d`. Proving (1) for every hard prime would be an even stronger claim than required. Neither sharpness families, nonresidue signs, square composites, nor finite factor checks prove this pointwise disjunction or provide a prime counterexample.
