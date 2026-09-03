import Submission.ShortTriangleBothChords

/-! A two-vertex support saving suffices for butterfly restoration, even with two components. -/
namespace Erdos583ButterflySupportBudgetDevelopment
open SimpleGraph Erdos583Work Erdos583Work.BridgeGlue
open Erdos583CorePathPiecesDevelopment Erdos583ButterflyRoutesDevelopment
open Erdos583ButterflyRestorationDevelopment Erdos583ButterflyAcrossComponentsDevelopment
open Erdos583ButterflySmoothingReductionDevelopment Erdos583TwoComponentBudgetDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma failure_no_butterfly_support_saving {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {F G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hFG : F ≤ G) (f : Fin 5 → Fin n) (hf : Function.Injective f)
    (ha : ∀ i, G.Adj (f (baseSource i)) (f (baseTarget i)))
    (hdis : Disjoint (coreEdges baseSource baseTarget f) F.edgeSet)
    (hcover : G.edgeSet=F.edgeSet ∪ coreEdges baseSource baseTarget f)
    (hhub : f 0 ∉ F.support) (hr : f 1 ∈ F.support)
    (hcF : F.support.ncard+2 ≤ n)
    (htwo : ∀ v ∈ F.support, F.Reachable (f 3) v ∨ F.Reachable (f 4) v) : False := by
  classical
  by_cases hF : SupportConnected F
  · obtain ⟨D,hD,hDc⟩ := LowDegreeAdjacency.smaller_orders_on_support hsmall F hF (by omega)
    apply failure_no_butterfly_partition hsmall hG hfail hFG f hf ha hdis hcover hhub ⟨1,hr⟩ D hD
    rw [ceil_half] at hDc
    simp only [Fintype.card_fin,ceil_half]
    omega
  · obtain ⟨h3,h4,h34⟩ := disconnected_two_reachable htwo hF
    obtain ⟨D,hD,hDc⟩ := smaller_orders_two_support_components hsmall F (by omega)
      (two_reachable_component_card h3 h4 htwo)
    have hlift : ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card := by
      rcases htwo (f 1) hr with h3r | h4r
      · exact restore_butterfly_across_components_four hFG f hf ha hdis hcover hhub hr h4
          (fun hh ↦ h34 (h3r.trans hh)) D hD
      · exact restore_butterfly_across_components hFG f hf ha hdis hcover hhub hr h3
          (fun hh ↦ h34 (h4r.trans hh).symm) D hD
    obtain ⟨E,hE,hEc⟩ := hlift
    apply hfail
    refine ⟨E,hE,?_⟩
    simp only [Fintype.card_fin,ceil_half]
    omega

end Erdos583ButterflySupportBudgetDevelopment
