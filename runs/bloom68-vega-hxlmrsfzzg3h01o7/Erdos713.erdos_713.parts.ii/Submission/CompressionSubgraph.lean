import Submission.PricedExtremizers

/-!
# Native loss and repairs after passing to a spanning subgraph

These finite comparisons apply to arbitrary simultaneous vertex maps. In
particular, deleting a common set of old edges to repair several individual
identifications does not evade the repair lower bound for their simultaneous
quotient. The balanced-cut and asymptotic consequences are working mathematics
in `PricedExtremizersProgress.md`; this file does not settle the conjecture.
-/

open SimpleGraph Erdos713Priced

namespace Erdos713CompressionSubgraph

universe u v w

variable {V : Type u} {U : Type v} {W : Type w}

/-- An actual simple quotient is monotone in the old graph. -/
theorem compression_mono {F G : SimpleGraph V} (hFG : F ≤ G) (π : V → U) :
    compression F π ≤ compression G π :=
  fromEdgeSet_mono (Set.image_mono (edgeSet_mono hFG))

section Finite

variable [Fintype V] [Fintype U]

open scoped Classical

/-- Native loop/parallel-edge loss cannot increase on a spanning subgraph. -/
theorem nativeLoss_mono {F G : SimpleGraph V} (hFG : F ≤ G) (π : V → U) :
    nativeLoss F π ≤ nativeLoss G π := by
  let D := G.edgeFinset \ F.edgeFinset
  have hdelete : G.deleteEdges (D : Set (Sym2 V)) = F := by
    simpa only [D, Finset.coe_sdiff, coe_edgeFinset] using
      G.deleteEdges_sdiff_eq_of_le hFG
  have hquot := compression_lost_card_le G π D
  rw [hdelete, Finset.card_sdiff_of_subset
    (edgeFinset_mono (compression_mono hFG π))] at hquot
  have hD : D.card = G.edgeFinset.card - F.edgeFinset.card :=
    Finset.card_sdiff_of_subset (edgeFinset_mono hFG)
  have hFGcard := Finset.card_le_card (edgeFinset_mono hFG)
  have hquotcard := Finset.card_le_card (edgeFinset_mono (compression_mono hFG π))
  have hF := nativeLoss_add_card F π
  have hG := nativeLoss_add_card G π
  omega

/-- After passing to any spanning subgraph, successful old-edge repair of an
arbitrary quotient still costs its excess over the target extremal number,
up to the original graph's native loss. No minimality of the repair is assumed. -/
theorem subgraph_repair_bound {F G : SimpleGraph V} (hFG : F ≤ G)
    (H : SimpleGraph W) (π : V → U) (D : Finset (Sym2 V))
    (hfree : H.Free (compression (F.deleteEdges (D : Set (Sym2 V))) π)) :
    F.edgeFinset.card ≤ extremalNumber (Fintype.card U) H +
      nativeLoss G π + D.card := by
  have htransfer := compression_repair_edge_transfer F π D
  have hloss := nativeLoss_mono hFG π
  have hex := card_edgeFinset_le_extremalNumber hfree
  omega

/-- A common deletion retaining at least half of the original edges cannot
make a simultaneous quotient cheap to repair merely because all single-pair
quotients have become free. This is an exact natural-number inequality. -/
theorem half_subgraph_repair_bound {F G : SimpleGraph V} (hFG : F ≤ G)
    (hhalf : G.edgeFinset.card ≤ 2 * F.edgeFinset.card)
    (H : SimpleGraph W) (π : V → U) (D : Finset (Sym2 V))
    (hfree : H.Free (compression (F.deleteEdges (D : Set (Sym2 V))) π)) :
    G.edgeFinset.card ≤ 2 * extremalNumber (Fintype.card U) H +
      2 * nativeLoss G π + 2 * D.card := by
  have h := subgraph_repair_bound hFG H π D hfree
  omega

/-- Explicit deficit form, allowing a real error allowance for the native
loss and an arbitrary guaranteed retained-edge fraction. -/
theorem subgraph_repair_real_bound {F G : SimpleGraph V} (hFG : F ≤ G)
    (H : SimpleGraph W) (π : V → U) (D : Finset (Sym2 V))
    (hfree : H.Free (compression (F.deleteEdges (D : Set (Sym2 V))) π))
    (θ E : ℝ)
    (hretain : θ * (G.edgeFinset.card : ℝ) ≤ (F.edgeFinset.card : ℝ))
    (hloss : (nativeLoss G π : ℝ) ≤ E) :
    θ * (G.edgeFinset.card : ℝ) - (extremalNumber (Fintype.card U) H : ℝ) - E ≤
      (D.card : ℝ) := by
  have h : (F.edgeFinset.card : ℝ) ≤
      (extremalNumber (Fintype.card U) H : ℝ) + (nativeLoss G π : ℝ) + D.card := by
    exact_mod_cast subgraph_repair_bound hFG H π D hfree
  linarith

/-- The exact global-price variant, with no extremal-number asymptotics and
no assertion that an increment of the extremal function is differentiable. -/
theorem priced_subgraph_repair_bound {F G : SimpleGraph V} (hFG : F ≤ G)
    {H : SimpleGraph W} {p : ℕ → ℝ} (hG : IsPricedExtremal H G p)
    (π : V → U) (D : Finset (Sym2 V))
    (hfree : H.Free (compression (F.deleteEdges (D : Set (Sym2 V))) π)) :
    p (Fintype.card V) - p (Fintype.card U) -
      ((G.edgeFinset.card : ℝ) - (F.edgeFinset.card : ℝ)) ≤
      (nativeLoss G π : ℝ) + D.card := by
  have htransfer : (F.edgeFinset.card : ℝ) ≤ (nativeLoss F π : ℝ) + D.card +
      ((compression (F.deleteEdges (D : Set (Sym2 V))) π).edgeFinset.card : ℝ) := by
    exact_mod_cast compression_repair_edge_transfer F π D
  have hloss : (nativeLoss F π : ℝ) ≤ (nativeLoss G π : ℝ) := by
    exact_mod_cast nativeLoss_mono hFG π
  have hcompare := hG.compare _ hfree
  linarith

end Finite

end Erdos713CompressionSubgraph
