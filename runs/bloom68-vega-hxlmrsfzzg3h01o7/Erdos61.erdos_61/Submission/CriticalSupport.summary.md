# CriticalSupport — verified standalone development

- Lean file: `Submission/CriticalSupport.lean`
- Namespace: `Auxiliary.CriticalSupport`
- Only direct import: `Submission.CriticalBlocker`

Write `n = Fintype.card V`, `A = G.indepNum`, and `W = G.cliqueNum`.
The development uses the existing `IsProductCritical` definition unchanged.

## Proven results

1. `card_pos_of_critical` and `card_eq_product_pow_add_one`:
   criticality implies `n > 0` and `n = (A * W)^k + 1`.
   The normalization actually holds for every natural `k`, including zero.
2. `single_deletion_parameters` (also separate independence/clique corollaries):
   for `1 ≤ k`, deleting any one vertex preserves both `A` and `W`.
3. `signedSupport`, `supportBag`, and `lowSupport` implement the requested
   singleton-inside / neighbors-outside convention, bags `X_J`, and sets `L_s`.
   For an independent host `B`, `t = B.card ≤ A` follows from independence.
   `supportBag_disjoint`, `supportBag_anticomplete`, and
   `supportBag_indepNum_le` prove the structural claims and
   `alpha(X_J) ≤ A - t + |J|`.
4. `critical_support_budget`: for `J ⊂ B`,
   `|X_J| ≤ ((A - t + |J|) * W)^k`.
5. `critical_partial_host_inequality`: for naturals `s ≤ m < t`,
   `|L_s| * choose(t-s, m-s) ≤ choose(t,m) * ((A-t+m) * W)^k`.
   The proof counts fixed-size supersets exactly, proves the required vertex
   multiplicity, and double-counts vertex/bag incidences.
6. Complement invariance and clique-host versions of the structural,
   support-budget, and partial-host results are included. Complementary
   support is nonneighbors outside the host and a singleton inside it.

The budget and partial-host theorems are also available under the weaker
`ProperInducedBound` hypothesis, without the strict counterexample assumption.
There are no unfinished requested extras and no claim to prove full EH or any
new forbidden-graph-dependent assertion.

## Verification

Strict compilation succeeded with:

```sh
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false \
  -DwarningAsError=true -Dwarn.sorry=true Submission/CriticalSupport.lean
```

All 34 public theorems have `#print axioms` checks. Their dependencies are
subsets of `{propext, Classical.choice, Quot.sound}`. There are no proof
placeholders, custom axioms, or options disabling checks. An import/API smoke
test and concrete signed-support and superset-count boundary tests also passed
with the same strict flags. A compiled `.olean` is available in the standard
`.lake/build/lib/lean/Submission/` directory.

SHA-256 checks confirmed that `Spec.lean` and all prior Submission modules
were unchanged.
