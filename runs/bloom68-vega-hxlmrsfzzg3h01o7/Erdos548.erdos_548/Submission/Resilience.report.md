# Resilience.lean — verified conditional Erdős–Sós bridge

## Result and scope

**Completed: a kernel-checked conditional bridge. R2 remains unproved.**

`Submission/Resilience.lean` proves the excess-deletion identity, the robust
universal consequence of a smaller-parameter induction hypothesis, an elementary
`k = 2` base case, and the exact original `+1` conclusion **conditional on a
uniform R2 hypothesis**. It does not assert either R2 or unconditional
Erdős–Sós.

The main file imports only:

```lean
import Submission.Auxiliary
import Submission.Critical
```

Both auxiliary files import only `FormalConjecturesUtil`. Neither `Spec.lean`
nor its declarations are imported or used. `Spec.lean`, `Auxiliary.lean`, and
`Critical.lean` are unchanged. No numerical experiment or other research report
is used as a premise.

All names below are in namespace `Erdos548.Resilience` unless qualified otherwise.

## Exact R2 interface

```lean
def TreeUniversal (k : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ T : SimpleGraph (Fin (k + 1)), T.IsTree → T.IsContained G

def RobustUniversal (j : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ F : Set (Sym2 V), F ⊆ G.edgeSet → F.ncard ≤ Nat.card V →
    TreeUniversal j (G.deleteEdges F)

def UniformR2 : Prop :=
  ∀ (k : ℕ), 3 ≤ k → ∀ {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → ⌈(k : ℚ) / 2⌉₊ ≤ G.minDegree → k ≤ G.maxDegree →
    RobustUniversal (k - 2) G → TreeUniversal k G
```

This is the original candidate: connected finite host, minimum degree at least
`ceil(k/2)`, maximum degree at least `k`, and universality for **every** smaller
tree after **every** deletion of **at most** the host order many actual edges.
It has **no extra density or criticality hypothesis**. The `Fintype` and
adjacency-decision instances permit the use of mathlib's degree definitions;
classical instances are available for any finite graph. Trees are labelled on
`Fin (k+1)`, matching the original target. `IsContained` means ordinary,
not necessarily induced, `Copy`.

The smaller assumption used internally is:

```lean
def UniformCriticalR2 : Prop :=
  ∀ (k : ℕ), 3 ≤ k → ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
    Erdos548.Critical.IsInducedCritical k G →
    RobustUniversal (k - 2) G → TreeUniversal k G
```

`uniformCriticalR2_of_uniformR2` proves

```text
UniformR2 → UniformCriticalR2.
```

**Direction matters:** criticality is a stronger condition on a host, so the
uniform assertion restricted to critical hosts is a weaker global assumption.
No converse or equivalence with the original R2 candidate is claimed. Critical
hosts have positive excess by definition. Their connectivity is newly proved in
`connected_of_inducedCritical`; their degree bounds use verified results from
`Critical.lean`. Thus the original degree/connectivity candidate, not merely a
modified substitute, suffices for the final conditional theorem.

## Exact deletion arithmetic and order bounds

`D k G` is rational-valued:

```text
D_k(G) = 2 e(G) - ((k : ℚ) - 1) Nat.card(V)
       = 2 * Erdos548.Critical.excess k G.
```

`D_deleteEdges` proves, for `[Finite V]`, `2 ≤ k`, and `F ⊆ G.edgeSet`:

```text
D_(k-2)(G.deleteEdges F) = D_k(G) + 2 * (Nat.card(V) - F.ncard).
```

Both subtractions on the right are rational. The natural subtraction in the
parameter `k - 2` is justified by `2 ≤ k`. The proof uses the exact natural
partition

```text
e(G.deleteEdges F) + F.ncard = e(G),
```

proved in `ncard_deleteEdges_add`. The identity itself does not require
`F.ncard ≤ n`; only the subsequent positive-excess conclusion requires that
budget. In particular, at `F.ncard = n` the double excess is exactly preserved.

Other relevant results:

* `excess_deleteEdges`: half-normalized version of the identity.
* `excess_deleteEdges_pos`: positive excess at `k` implies positive excess at
  `k-2` after **any** allowed deletion, including the full budget.
* `card_ge_of_excess_pos`: positive excess implies `k + 1 ≤ Nat.card V`.
* `card_ge_after_deletion`: every damaged host satisfies
  `(k - 2) + 1 ≤ Nat.card V`.

The order bounds are derived from an existing degree-at-least-`k` vertex and
`degree < order`. They are not assumed for critical subgraphs or deleted
hosts. Empty hosts cannot have positive excess, including when `k = 0`.

## Induction and base cases

`StrictAt k` quantifies over **all finite hosts**, without connectivity or degree
restrictions:

```text
positive excess at k → TreeUniversal k G.
```

Its explicit order bound is redundant by `card_ge_of_excess_pos`.
`robustUniversal_of_strictAt` proves the logically essential implication

```text
StrictAt (k-2) + positive excess at k
  → RobustUniversal (k-2) G                     (2 ≤ k).
```

Each deletion gets its own application of the smaller universal statement.
No common embedding is required across different deletions or different trees.
The damaged graph may be disconnected and may lose all the original degree or
criticality properties.

`strictAt_of_uniformCriticalR2` uses strong induction on `k`:

* `k = 0,1`: the verified elementary lemmas from `Auxiliary.lean` apply; the
  one-vertex case obtains nonemptiness from positive excess.
* `k = 2`: `strictAt_two` is proved here, with no R2 premise. Density `e > n/2`
  gives a vertex with two distinct neighbors. A three-vertex tree omits one of
  the three possible edges, so it has an ordinary copy in those three host
  vertices. Extra host edges do not matter.
* `k ≥ 3`: the verified positive-excess reduction gives an induced-critical
  host. The recursive hypothesis is used **only at `k-2 < k`**, uniformly over
  all deleted hosts. The assumed critical R2 gives a copy of each larger tree,
  which is composed with the inclusion of the induced host into the original
  graph.

The critical reduction is selected using positive excess alone, not a presumed
failure or success of the desired embedding. There is no circular invocation of
Erdős–Sós at the current parameter.

## Main conditional results

* `strictAt_of_uniformCriticalR2`:
  `UniformCriticalR2 → ∀ k, StrictAt k`.
* `strictAt_of_uniformR2`:
  `UniformR2 → ∀ k, StrictAt k`.
* `strictThresholdStatement_of_uniformR2`:
  `UniformR2.{0} → Erdos548.Auxiliary.StrictThresholdStatement`.
* `plusOneStatement_of_uniformR2`:
  `UniformR2.{0} → Erdos548.Auxiliary.PlusOneStatement`.
* `erdos_548_of_uniformR2`: the exact original target interface:

```lean
theorem erdos_548_of_uniformR2 (hR2 : UniformR2.{0}) :
    ∀ (n k : ℕ), k + 1 ≤ n → ∀ G : SimpleGraph (Fin n),
      ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ) →
        ∀ T : SimpleGraph (Fin (k + 1)), T.IsTree → T.IsContained G
```

The verified strict-to-`+1` implication from `Auxiliary.lean` is used, not a
pointwise substitution of inequivalent threshold hypotheses. The results above
are conditional on their explicit R2 parameter; no inhabitant of either R2
proposition is constructed.

## Verification

Verified with **Lean 4.27.0 / mathlib v4.27.0**. From `/workspace/leanproject`:

```bash
mkdir -p .lake/build/lib/lean/Submission
lake env lean -o .lake/build/lib/lean/Submission/Auxiliary.olean \
  -i .lake/build/lib/lean/Submission/Auxiliary.ilean Submission/Auxiliary.lean
lake env lean -o .lake/build/lib/lean/Submission/Critical.olean \
  -i .lake/build/lib/lean/Submission/Critical.ilean Submission/Critical.lean
lake env lean -o .lake/build/lib/lean/Submission/Resilience.olean \
  -i .lake/build/lib/lean/Submission/Resilience.ilean Submission/Resilience.lean
lake env lean -o .lake/build/lib/lean/Submission/ResilienceVerification.olean \
  -i .lake/build/lib/lean/Submission/ResilienceVerification.ilean \
  Submission/ResilienceVerification.lean
lake env lean --deps Submission/Resilience.lean
```

All commands succeed. The main file and verification file compile without
warnings or errors.

The main file ends with `#print axioms` for **all 22 theorems**. Every result
uses only `propext`, `Classical.choice`, and `Quot.sound`, or no axioms. There is
no `sorryAx`, `sorry`, `admit`, `native_decide`, or newly declared axiom in the
new proofs.

`ResilienceVerification.lean` contains **11 compiled interface/boundary
examples**: the `k=2` identity endpoint; the exact full deletion budget; no edge
deletions; the negative coefficient at `k=0`; empty hosts; all critical-host
side conditions and order; the elementary base without an order assumption;
the robust consequence with a derived order bound; the original R2 interface
without density; the exact target as an ordinary `Copy`; and the weaker
critical assumption's `+1` consequence.

It additionally checks the actual Lean environment and fails if either
`Erdos548.erdos_548` or `Erdos548.erdos_548.disproof` is present. Neither is
present. The direct dependency list for the main file contains only `Init`,
`Submission.Auxiliary`, and `Submission.Critical`.

### Artifacts

* `Submission/Resilience.lean` — requested implementation and all theorem audits.
* `Submission/ResilienceVerification.lean` — boundary/interface and environment checks.
* `Submission/Resilience.verification.log` — successful build and audit output.
* `Submission/Resilience.verification.json` — machine-readable results and theorem index.
* `Submission/Resilience.report.md` — this report.
* `.lake/build/lib/lean/Submission/Resilience{,Verification}.{olean,ilean}` — compiled outputs.

### SHA256 source checks

* New main file:
  `bbd948cdc0546b70756069a3a4339abcee6e22be371e65610cac05f7a6048a5b`
* New verification file:
  `d586e0f9a545390676e86cde9203386b565f60415f64386bb34f172605004747`
* Unchanged `Submission/Spec.lean`:
  `674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103`
* Unchanged `Submission/Auxiliary.lean`:
  `227fcc37cac1313bd1d9c8033397195fa990f018c784ba9a53e307f6ef1e28c1`
* Unchanged `Submission/Critical.lean`:
  `c0dc0d37acc9f1ca3173b6d144e326ccfcbf5a63eb98216fa6099e055b9d71ea`
