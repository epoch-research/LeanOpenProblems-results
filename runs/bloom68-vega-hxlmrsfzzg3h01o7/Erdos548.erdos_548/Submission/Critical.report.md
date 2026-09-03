# Critical.lean — completed infrastructure

## Status

Both requested pieces of infrastructure are implemented and kernel-checked in
`/workspace/leanproject/Submission/Critical.lean` on **Lean 4.27.0 / mathlib v4.27.0**.
The file's only import is `FormalConjecturesUtil`. It does not import or use
`Submission.Spec` or `Submission.Auxiliary`; both protected source files are unchanged.
No full Erdős–Sós theorem is asserted or proved.

## 1. Finite-tree embedding

All names below are fully qualified.

* `Erdos548.Critical.isContained_of_isTree_of_card_eq_succ_of_minDegree`:
  for arbitrary `Fintype` vertex types, a tree `T` with `Fintype.card A = m + 1`
  is contained in a nonempty finite host `G` if `m ≤ G.minDegree`.
* `Erdos548.Critical.isContained_of_isTree_of_minDegree`:
  the same theorem with hypothesis `Fintype.card A - 1 ≤ G.minDegree`.
* `Erdos548.Critical.isContained_of_isTree_of_card_eq_succ_of_neighborSet_ncard`:
  the `Finite`-only version, using `Nat.card A = m + 1` and
  `∀ v, m ≤ (G.neighborSet v).ncard`. No enumeration or decidable-adjacency
  instance is required in this statement.
* `Erdos548.Critical.fin_tree_isContained_of_minDegree`:
  the `Fin` specialization, for `T : SimpleGraph (Fin (m + 1))` and
  `G : SimpleGraph (Fin n)`, with `m + 1 ≤ n` and `m ≤ G.minDegree`.

The conclusion `T.IsContained G` is definitionally `Nonempty (T.Copy G)`:
it is an **ordinary**, not necessarily induced, copy. An interface example checks
that exact type. The proof uses strong induction on tree order, deletion of a
leaf through a vertex subtype, and a fresh neighbor outside the old copy's range.
The fresh-neighbor lemma is `Erdos548.Critical.exists_adj_not_mem_range`.

The nonempty-host condition is necessary for `m = 0`: mathlib assigns minimum
degree zero to an empty host, which cannot contain a one-vertex tree.

## 2. Positive-excess induced critical reduction

`Erdos548.Critical.excess k G` is

```
(G.edgeSet.ncard : ℚ) - ((k : ℚ) - 1) / 2 * Nat.card V
```

Thus `k - 1` is rational subtraction, including at `k = 0`.
`Erdos548.Critical.IsInducedCritical k H` means positive excess and nonpositive
excess for every proper induced subgraph (including the empty one).

Main existence results:

* `Erdos548.Critical.exists_induced_critical_of_edge_threshold`:
  under `[Finite V]` and the strict edge threshold, gives a nonempty vertex set
  `s` such that `H = G.induce s` is critical.
* `Erdos548.Critical.exists_critical_reduction`:
  packages that conclusion together with all incident-set inequalities and the
  two degree consequences. It is entirely `Finite`-based: the degree clauses are
  `∀ x, ceil(k/2) ≤ (H.neighborSet x).ncard` and
  `∃ x, k ≤ (H.neighborSet x).ncard`.

Unpacked consequences:

* `Erdos548.Critical.IsInducedCritical.edge_threshold`: `e(H) > c |V(H)|`.
* `Erdos548.Critical.IsInducedCritical.proper_edge_threshold`:
  `e(H[t]) ≤ c |t|` for every proper vertex set `t`, where `c = ((k : ℚ)-1)/2`.
* `Erdos548.Critical.IsInducedCritical.incidentEdges_bound`:
  for every **nonempty** set `t`, `c |t| < |incidentEdges H t|`.
* `Erdos548.Critical.IsInducedCritical.minDegree_ge_ceil`:
  `⌈(k : ℚ) / 2⌉₊ ≤ H.minDegree`.
* `Erdos548.Critical.IsInducedCritical.minDegree_ge_half`:
  `(k + 1) / 2 ≤ H.minDegree`.
* `Erdos548.Critical.IsInducedCritical.maxDegree_ge`: `k ≤ H.maxDegree`.
* `Erdos548.Critical.maxDegree_ge_of_excess_pos`: the maximum-degree bound
  actually needs only positive excess, not criticality.

`Erdos548.Critical.incidentEdges H t` is the set of edges with at least one
endpoint in `t`; internal edges count once. The exact partition identity
`Erdos548.Critical.ncard_induce_compl_add_incidentEdges` proves

```
e(H[tᶜ]) + |incidentEdges H t| = e(H).
```

Minimum-cardinality choice among positive-excess induced subgraphs gives
criticality. Subtracting the proper-complement threshold using the exact
partition gives the incident bound. Integrality supplies the ceiling degree
bound; the degree-sum formula gives the maximum-degree bound.

The incident inequality must exclude `t = ∅`, where both sides are zero.
All critical reduction statements allow `k = 0`. They yield minimum degree
`ceil(k/2)`, **not** minimum degree `k`, so they do not close the Erdős–Sós gap.

## Verification

The following commands succeeded without errors or warnings:

```bash
cd /workspace/leanproject
mkdir -p .lake/build/lib/lean/Submission
lake env lean -o .lake/build/lib/lean/Submission/Critical.olean \
  -i .lake/build/lib/lean/Submission/Critical.ilean Submission/Critical.lean
lake env lean Submission/CriticalVerification.lean
lake env lean --deps Submission/Critical.lean
```

`Critical.lean` ends with `#print axioms` for **all 38 theorems**. Every audit
uses only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`
(or no axioms for `isContained_of_subsingleton`). There is no `sorryAx`,
`native_decide`, `sorry`, `admit`, or newly declared axiom.

`CriticalVerification.lean` contains seven compiled interface/boundary examples:
ordinary `Copy` on `Finite` types; the one-vertex embedding; impossibility in an
empty host; the negative threshold at `k = 0` on an edgeless singleton; no positive
excess in an empty graph; the full `Fin n` edge-threshold interface; and zero
incident edges for the empty vertex set.

Artifacts:

* `Submission/Critical.lean` — standalone proved infrastructure and axiom checks.
* `Submission/CriticalVerification.lean` — interface and boundary examples.
* `Submission/Critical.verification.log` — compiler, axiom, and audit output.
* `Submission/Critical.verification.json` — machine-readable verification and theorem index.
* `Submission/Critical.report.md` — this report.
* `.lake/build/lib/lean/Submission/Critical.olean` and `.ilean` — compiled outputs.

Source SHA256: `c0dc0d37acc9f1ca3173b6d144e326ccfcbf5a63eb98216fa6099e055b9d71ea`.

Protected-file SHA256s (unchanged):

* `Submission/Spec.lean`: `674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103`
* `Submission/Auxiliary.lean`: `227fcc37cac1313bd1d9c8033397195fa990f018c784ba9a53e307f6ef1e28c1`

## Complete theorem index

* `Erdos548.Critical.exists_adj_not_mem_range`
* `Erdos548.Critical.isContained_of_subsingleton`
* `Erdos548.Critical.isContained_of_isTree_of_card_le_degree_add_one`
* `Erdos548.Critical.isContained_of_isTree_of_minDegree`
* `Erdos548.Critical.isContained_of_isTree_of_card_eq_succ_of_minDegree`
* `Erdos548.Critical.isContained_of_isTree_of_neighborSet_ncard`
* `Erdos548.Critical.isContained_of_isTree_of_card_eq_succ_of_neighborSet_ncard`
* `Erdos548.Critical.fin_tree_isContained_of_minDegree`
* `Erdos548.Critical.ncard_edgeSet_iso`
* `Erdos548.Critical.excess_iso`
* `Erdos548.Critical.excess_induce_univ`
* `Erdos548.Critical.excess_of_isEmpty`
* `Erdos548.Critical.nonempty_of_excess_pos`
* `Erdos548.Critical.exists_induced_critical`
* `Erdos548.Critical.exists_induced_critical_of_edge_threshold`
* `Erdos548.Critical.incidentEdges_empty`
* `Erdos548.Critical.incidentEdges_singleton`
* `Erdos548.Critical.ncard_incidentEdges_singleton`
* `Erdos548.Critical.image_edgeSet_induce`
* `Erdos548.Critical.ncard_edgeSet_induce`
* `Erdos548.Critical.edgeSet_diff_incidentEdges`
* `Erdos548.Critical.ncard_induce_compl_add_incidentEdges`
* `Erdos548.Critical.IsInducedCritical.nonempty`
* `Erdos548.Critical.IsInducedCritical.edge_threshold`
* `Erdos548.Critical.IsInducedCritical.proper_edge_threshold`
* `Erdos548.Critical.IsInducedCritical.incidentEdges_bound`
* `Erdos548.Critical.IsInducedCritical.neighborSet_bound`
* `Erdos548.Critical.IsInducedCritical.two_mul_neighborSet_ncard_ge`
* `Erdos548.Critical.IsInducedCritical.neighborSet_ncard_ge_ceil`
* `Erdos548.Critical.ncard_neighborSet_eq_degree`
* `Erdos548.Critical.IsInducedCritical.two_mul_minDegree_ge`
* `Erdos548.Critical.IsInducedCritical.minDegree_ge_ceil`
* `Erdos548.Critical.IsInducedCritical.minDegree_ge_half`
* `Erdos548.Critical.exists_degree_ge_of_excess_pos`
* `Erdos548.Critical.maxDegree_ge_of_excess_pos`
* `Erdos548.Critical.exists_neighborSet_ncard_ge_of_excess_pos`
* `Erdos548.Critical.IsInducedCritical.maxDegree_ge`
* `Erdos548.Critical.exists_critical_reduction`
