# E30 all-height bridge — conditional results only

## Status and files

Implemented `Submission/E30HeightBridge.lean` (395 lines), importing only
`Submission.E30Bridge`. All declarations are in `Erdos30Research`.

- Kernel audit and semantic tests: `Submission/E30HeightBridgeAudit.lean`.
- Rebuild, theorem signatures, axiom output, and checksums:
  `Submission/E30HeightBridgeAudit.log`.
- This report: `Submission/E30HeightBridgeReport.md`.

**No unbounded family is constructed. No proof or disproof of the original
Erdős 30 target is claimed. `Submission/Spec.lean` was neither imported nor edited.**

## Exact sufficient criterion

The finite index is

```lean
HeightIndex m A := A ⊕ Fin (m - 1)
```

where `A : Finset ℤ`. A heavy index `a` has coordinates `(0,a)`; a light
index `s` has coordinates `(s.val+1, b(s.val+1))`. The integer mark is
`heightMark m r v i = r i + m*v i`. `liftMark_injective` proves this explicit
map injective whenever `m > 0`. Thus it gives precisely the heavy marks `m*A`
and exactly one light mark in each residue `1,...,m-1`.

For an ordered edge `e=(i,j)` define

```text
R(e) = r(i)-r(j) + (if r(i)<r(j) then m else 0)
H(e) = v(i)-v(j) + (if r(i)<r(j) then -1 else 0).
```

`edge_data` proves `0 ≤ R(e) < m` and the exact difference identity
`mark(i)-mark(j) = R(e)+m*H(e)`. `edge_quotient_remainder` proves

```text
R(e) = (r(i)-r(j)) % m
H(e) = v(i)-v(j) + (r(i)-r(j))/m.
```

`EdgeRowsInjective m r v` is the explicit, multiplicity-preserving test

```lean
∀ t : ℤ, 0 < t → t < m → Function.Injective
  (fun e : {e : ι × ι // edgeResidue m r e = t} => edgeHeight r v e.val)
```

It is not an assumption that the whole mark set is Sidon. In a nonzero row
`t`, its edge values are exactly the four requested kinds:

1. `b_t-a` (light destination, heavy source);
2. `a-b_(m-t)-1` (heavy destination, light source, including the seam);
3. `b_(s+t)-b_s` for `1 ≤ s < m-t`;
4. `b_(s+t-m)-b_s-1` for `m-t < s < m`.

`heavy_light_carries` and `light_light_carry` expose the height formulas;
the general quotient/remainder theorem certifies their residue assignment.
The domain retains endpoint identities, so equal values from different parts
of the multiset are rejected rather than silently deduplicated.

Key sufficient theorem (abbreviating only the displayed marking functions):

```lean
allHeight_isSidon (hm : 2 ≤ m) (hA : IsSidon (A : Set ℤ))
  (hrows : EdgeRowsInjective (m : ℤ) (@liftResidue m A) (liftHeight b)) :
  IsSidon (Set.range
    (heightMark (m : ℤ) (@liftResidue m A) (liftHeight b)))
```

`same_residue_heavy` proves that distinct endpoints in a zero-residue edge
must both be heavy, so strong Sidonicity of `A` supplies exactly the remaining
zero-row test. `int_isSidon_iff_differences` proves strong Sidonicity, including
doubled summands, equivalent to uniqueness of nonzero ordered differences.
`isSidon_of_edge_rows` supplies the more general fibre criterion.

The finite-index modulus is a natural number at least two, representing every
integer modulus at least two; the general fibre and carry lemmas use `m : ℤ`.
All heights are unrestricted integers until a box is explicitly assumed.

## Box, cardinality, and exact target accounting

`nat_set_of_integer_marks` explicitly takes the image of
`i ↦ (mark(i)+1).toNat`. Under `0 ≤ mark(i) < N`, it preserves injectivity,
cardinality, and strong Sidonicity.

`allHeight_nat_set` assumes the sufficient criterion and all heavy/light
heights in the ordinary interval `[0,L]`. It proves

```lean
∃ B : Finset ℕ, B ⊆ Finset.Icc 1 (m * (L + 1)) ∧
  IsSidon (B : Set ℕ) ∧ B.card = m - 1 + A.card
```

The proof first bounds every integer mark in `[0,m*(L+1))` and then translates
by `+1`. There is no reduction of heights modulo any parent period.

`AllHeightBox p L` packages the explicit data `A,b`, strong Sidonicity of `A`,
`A.card=p+1`, the nonzero row-injection test, and the two height bounds, with
`m=p²-p+1`. It does not assume Sidonicity of the lifted set and asserts no
existence. `AllHeightBox.nat_set`, for `p≥2`, gives

```text
N = (p²-p+1)*(L+1),    B.card = p²+1.
```

`target_modulus_card` proves the exact natural cardinality identity and `m≥2`.
`target_diameter_identity`, for `p≥2`, `L : ℕ`, `G : ℤ`, proves

```text
L+1 = p²+p+1-G  ==>  (p²+1)² - N = p²+(p²-p+1)*G.
```

The latter subtraction is in `ℤ`. All casts of `p²-p` are justified; no
truncated-subtraction identity is assumed.

## Conditional analytic connection — including the real-power algebra

`not_all_power_bounds_of_allHeight_saving` assumes fixed `α,c>0` and

```text
for every P there are p≥P, p≥2, L, and C : AllHeightBox p L such that
N ≤ k²-c*k^(1+α), where N=m*(L+1), k=p²+1.
```

It invokes the existing `not_all_power_bounds_of_diameter_saving`, supplying
unbounded `k`, the finite natural Sidon set, its box, and its exact cardinality.
Its conclusion is failure of all positive-power Big-O error bounds for the
existing `Erdos30Research.h`.

The real-power step is also proved, not left as a gap.
`diameter_saving_of_height_gap` proves, for real `p≥2`, `c₀,β>0`,
`L+1=p²+p+1-G`, and `G≥c₀*p^β`,

```text
N ≤ k²-c*k^(1+α),
α = β/2,
c = (c₀/2) / 2^(1+β/2) > 0.
```

This uses the simple bounds `m≥p²/2` and `k≤2p²`; the constant is intentionally
not optimized.

Consequently `not_all_power_bounds_of_allHeight_gap` has the precise hypothesis

```lean
∀ P : ℕ, ∃ p ≥ P, 2 ≤ p ∧ ∃ L : ℕ, ∃ _ : AllHeightBox p L, ∃ G : ℤ,
  (L : ℤ) + 1 = (p : ℤ)^2 + p + 1 - G ∧ c₀ * (p : ℝ)^β ≤ (G : ℝ)
```

for fixed `β,c₀>0`, and concludes

```lean
¬ (∀ ε : ℝ, 0 < ε →
  (fun N : ℕ => (h N : ℝ) - Real.sqrt (N : ℝ)) =O[atTop]
    (fun N : ℕ => (N : ℝ)^ε))
```

**The entire family hypothesis remains unproved.** Constructing compatible
heavy/light data in short enough boxes along unbounded `p` is the substantive
remaining mathematical task. No primality assumption is needed for these
conditional reductions. The cyclic-word reconstruction from the external
research report is not formalized here and is not used.

## Reproduction and verification

From `/workspace/leanproject`:

```sh
lake env lean -o .lake/build/lib/lean/Submission/E30Bridge.olean Submission/E30Bridge.lean
lake env lean -o .lake/build/lib/lean/Submission/E30HeightBridge.olean Submission/E30HeightBridge.lean
lake env lean Submission/E30HeightBridgeAudit.lean
sha256sum Submission/Spec.lean
```

All three Lean commands pass without warnings or errors. The audit prints
axioms for every top-level declaration in the new helper; dependencies are
only subsets of `{propext, Classical.choice, Quot.sound}`. It also kernel-checks
negative heights, both light-light carry branches, the heavy seam, the
`0+2=1+1` collision, rejection by the row test of the non-Sidon lift of the
Sidon heavy set `{0,1}`, a generic necessity check for nonzero row injections,
a sample exact target identity, and positivity of the saving constant.

The protected file checksum remains

```text
9ffc327c4d7d8a5c18d2b3a5e4ad04270ebbdcf797bfa372c715f3673c5ca944
```
