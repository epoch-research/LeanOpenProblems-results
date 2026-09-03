# Lean formalization of finite CL

## Status

**Complete.** `Submission/CommonMarkedForest.lean` proves the finite common-list marked-forest theorem, independently of `Submission.Spec`. Its only import is `Mathlib`. It compiles with Lean/mathlib v4.27.0, with no warnings or errors. There are no unfinished lemmas, extra axioms, `sorry`, `admit`, or native-evaluation proof shortcuts.

The transitive axiom sets of all main theorems are exactly:

```
[propext, Classical.choice, Quot.sound]
```

An exhaustive audit of the file's 61 public declarations also found only subsets of these axioms; the private gluing helpers are included transitively. The audit output is in `Submission/CommonMarkedForestLeanAudit.log`.

## Main interface

In namespace `CommonMarkedForest`:

```lean
theorem CL {V : Type u} [Fintype V]
    (F : SimpleGraph V) (hF : F.IsAcyclic)
    (roots : F.ConnectedComponent → V)
    (hroots : ∀ C, roots C ∈ C)
    {W : Type v} [Fintype W]
    (H : SimpleGraph W) (A : Set W)
    (hdeg : F.edgeSet.ncard ≤ H.minDegree)
    (hA : Fintype.card V ≤ A.ncard) :
    ∃ f : F.Copy H, ∀ C, f (roots C) ∈ A
```

`SimpleGraph.Copy` is Mathlib's injective homomorphism, **not** its induced-embedding type. A returned copy has `f.toHom : F →g H` and `f.injective : Function.Injective f.toHom`.

There are no nonempty-host, nonempty-forest, or nonisolated-component assumptions. All graphs here are finite. The result does not prescribe an individual host image for each root: all roots must merely land in the same set `A`.

Useful additional interfaces:

* `common_list_forest`: subtype-valued roots `(C : F.ConnectedComponent) → C`, a `Finset` common list, and a vertexwise degree hypothesis `∀ s, F.edgeFinset.card ≤ H.degree s`.
* `common_list_forest_roots`: the same `Finset`/vertexwise-degree interface, with vertex-valued roots and component-membership proofs.
* `common_list_family`: a finite family `T : I → RootedTree`, with degree threshold `totalEdges T` and list threshold `totalOrder T`, produces a marked copy of `forestGraph T`.

A `RootedTree` has a finite vertex type, an ordinary `SimpleGraph`, a proof of `IsTree`, and a specified root. Singletons are allowed. The file proves `totalOrder T = totalEdges T + Fintype.card I`, proves that `totalEdges T` is the actual edge cardinality of `forestGraph T`, and constructs a graph isomorphism from an acyclic graph's component-family union to the original graph. Thus the family formulation imposes no additional hypothesis on the final forest theorem.

## Connection with the mathematical proof

The formal proof implements the component-count induction, the clique meeting `A`, a fixed leaf-deleted rooted copy with a designated parent image, universal coverage of `X`, and root-sensitive swaps. It treats an isolated component by placing it at an unused allowed vertex after embedding the remaining family.

The four-class count is written in an equivalent sum-ready form. For each remaining component, let `M_i` count its image vertices missed by the outside vertex and let `Y_i` count its image vertices outside `X`. The proved `component_deficit` lemma gives

```
2 ≤ M_i + Y_i
```

when the outside vertex belongs to `A`, or when the component is not a root-centered star, and no legal switch is possible. Summing and using `|B| = b + q` and `|X| = b + 1` proves the required residual-degree bound `a + 1` in `H - B`. No bound in `H - (K ∪ B)` is asserted.

The two final branches are separate: a root-centered star uses the degree bound only at the unused allowed vertex; the other branch uses the proved clique-plus-outside tree-extension lemma in `H - B`. Selecting a root-centered star first makes the latter branch valid for every remaining component.

Key reusable lemmas include `exists_leaf_ne`, `tree_copy_of_fresh`, `tree_copy_minDegree`, `tree_copy_clique_outside`, `clique_of_universal_extensions`, `leaf_reservoir`, `copy_switch`, `component_deficit`, and `residual_degree`.

## Verification

From `/workspace/leanproject`:

```sh
lake env lean Submission/CommonMarkedForest.lean
lake env lean -o /tmp/CommonMarkedForest.olean Submission/CommonMarkedForest.lean
python3 Submission/CommonMarkedForestChecks.py --random 30000
```

Both Lean commands succeeded. The file itself prints the axiom sets of the main interfaces. The constructive checker, which was not modified, also passed:

* 1,839,848 local-switch configurations;
* 149,268 clique-plus-outside extension cases;
* 362,970 constructive atlas CL instances;
* 79,782 atlas prescribed-apex corollary instances;
* 26,785 CL instances from 30,000 random trials.

Both final branches and both root-moving and root-preserving switches were exercised. The checker output is stored in `Submission/CommonMarkedForestChecks.log`. These finite checks are corroboration; the general finite theorem is proved by Lean, not inferred from the checks.

`Submission/Spec.lean` was not modified. Its SHA-256 remains:

```
674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103
```

The infinite-host variant and the consequences in Section 5 of `CommonMarkedForestCL.md` are not formalized in this file. No unrestricted Erdős–Sós or unrestricted `W_k` embedding theorem is claimed.
