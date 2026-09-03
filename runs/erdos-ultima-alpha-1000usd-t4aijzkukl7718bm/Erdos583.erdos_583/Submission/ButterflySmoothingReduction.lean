import Submission.SmoothReachability

/-! Smoothing one outer vertex before restoring a butterfly, with both support-connectivity cases. -/
namespace Erdos583ButterflySmoothingReductionDevelopment
open SimpleGraph Erdos583Work Erdos583Work.BridgeGlue
open Erdos583CorePathPiecesDevelopment Erdos583ButterflyRoutesDevelopment
open Erdos583ButterflyPairsDevelopment Erdos583ButterflyRestorationDevelopment
open Erdos583ButterflyAcrossComponentsDevelopment Erdos583SupportSmoothingDevelopment
open Erdos583SmoothReachabilityDevelopment Erdos583TwoComponentBudgetDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma restore_butterfly_across_components_four {V : Type*} [Fintype V] {F G : SimpleGraph V}
    (hFG : F ≤ G) (f : Fin 5 → V) (hf : Function.Injective f)
    (ha : ∀ i, G.Adj (f (baseSource i)) (f (baseTarget i)))
    (hdis : Disjoint (coreEdges baseSource baseTarget f) F.edgeSet)
    (hcover : G.edgeSet=F.edgeSet ∪ coreEdges baseSource baseTarget f)
    (hhub : f 0 ∉ F.support) (hx : f 1 ∈ F.support) (hz : f 4 ∈ F.support)
    (hnon : ¬F.Reachable (f 1) (f 4))
    (D : Finset F.Subgraph) (hD : GoodDecomposition F D) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card := by
  let g := f ∘ Equiv.swap (3 : Fin 5) 4
  have hg : Function.Injective g := hf.comp (Equiv.swap (3 : Fin 5) 4).injective
  have hga : ∀ i, G.Adj (g (baseSource i)) (g (baseTarget i)) := by
    intro i
    fin_cases i
    · simpa [g,Equiv.swap_apply_def,baseSource,baseTarget] using ha 0
    · simpa [g,Equiv.swap_apply_def,baseSource,baseTarget] using ha 1
    · simpa [g,Equiv.swap_apply_def,baseSource,baseTarget] using ha 2
    · simpa [g,Equiv.swap_apply_def,baseSource,baseTarget] using (ha 5).symm
    · simpa [g,Equiv.swap_apply_def,baseSource,baseTarget] using (ha 4).symm
    · simpa [g,Equiv.swap_apply_def,baseSource,baseTarget] using (ha 3).symm
  have hge : coreEdges baseSource baseTarget g=coreEdges baseSource baseTarget f := by
    rw [base_coreEdges_eq,base_coreEdges_eq]
    ext e
    simp [g,Equiv.swap_apply_def,Sym2.eq_swap,or_comm,or_left_comm]
  apply restore_butterfly_across_components hFG g hg hga
    (by rwa [hge]) (by rwa [hge]) _ _ _ _ D hD
  · simpa [g,Equiv.swap_apply_def] using hhub
  · simpa [g,Equiv.swap_apply_def] using hx
  · simpa [g,Equiv.swap_apply_def] using hz
  · simpa [g,Equiv.swap_apply_def] using hnon

lemma failure_no_smooth_butterfly {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {F G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hFG : F ≤ G) (f : Fin 5 → Fin n) (hf : Function.Injective f)
    (ha : ∀ i, G.Adj (f (baseSource i)) (f (baseTarget i)))
    (hdis : Disjoint (coreEdges baseSource baseTarget f) F.edgeSet)
    (hcover : G.edgeSet=F.edgeSet ∪ coreEdges baseSource baseTarget f)
    (hhub : f 0 ∉ F.support) (hr : f 1 ∈ F.support)
    {c d : Fin n} (hyc : F.Adj (f 2) c) (hyd : F.Adj (f 2) d) (hcd : c ≠ d)
    (hNy : ∀ v, F.Adj (f 2) v → v=c ∨ v=d) (hncd : ¬F.Adj c d)
    (htwo : ∀ v ∈ F.support, F.Reachable (f 3) v ∨ F.Reachable (f 4) v) : False := by
  classical
  let H := smooth F (f 2) c d
  have hcF : F.support.ncard+1 ≤ n := by
    have hh := (insert (f 0) F.support).ncard_le_card
    rw [Set.ncard_insert_of_notMem hhub,Nat.card_eq_fintype_card,Fintype.card_fin] at hh
    exact hh
  have hcH : H.support.ncard+2 ≤ n := by
    have hh : H.support.ncard+1 ≤ F.support.ncard := smooth_support_card hyc hyd
    omega
  by_cases hF : SupportConnected F
  · have hH : SupportConnected H := smooth_support_connected hF hyc hyd hcd hNy
    obtain ⟨D,hD,hDc⟩ := LowDegreeAdjacency.smaller_orders_on_support hsmall H hH (by omega)
    obtain ⟨E,hE,hEc⟩ := smooth_lift hyc hyd hcd hNy hncd D hD
    apply failure_no_butterfly_partition hsmall hG hfail hFG f hf ha hdis hcover hhub ⟨1,hr⟩ E hE
    rw [ceil_half] at hDc
    simp only [Fintype.card_fin,ceil_half]
    omega
  · obtain ⟨h3,h4,h34⟩ := disconnected_two_reachable htwo hF
    have h32 : f 3 ≠ f 2 := fun he ↦ (by decide : (3 : Fin 5) ≠ 2) (hf he)
    have h42 : f 4 ≠ f 2 := fun he ↦ (by decide : (4 : Fin 5) ≠ 2) (hf he)
    have hHe : H.support=F.support \ {f 2} := smooth_support_eq hyc hyd hcd hNy
    have h3H : f 3 ∈ H.support := hHe.symm ▸ ⟨h3,h32⟩
    have h4H : f 4 ∈ H.support := hHe.symm ▸ ⟨h4,h42⟩
    have htwoH : ∀ v ∈ H.support, H.Reachable (f 3) v ∨ H.Reachable (f 4) v := by
      intro v hv
      have hv' : v ∈ F.support \ {f 2} := hHe ▸ hv
      rcases htwo v hv'.1 with h | h
      · exact Or.inl (smooth_reachable_forward hcd hyc hyd hNy h32 hv'.2 h)
      · exact Or.inr (smooth_reachable_forward hcd hyc hyd hNy h42 hv'.2 h)
    obtain ⟨D,hD,hDc⟩ := smaller_orders_two_support_components hsmall H (by omega)
      (two_reachable_component_card h3H h4H htwoH)
    obtain ⟨E,hE,hEc⟩ := smooth_lift hyc hyd hcd hNy hncd D hD
    have hlift : ∃ J : Finset G.Subgraph, GoodDecomposition G J ∧ J.card ≤ E.card := by
      rcases htwo (f 1) hr with h3r | h4r
      · apply restore_butterfly_across_components_four hFG f hf ha hdis hcover hhub hr h4
          (fun hh ↦ h34 (h3r.trans hh)) E hE
      · apply restore_butterfly_across_components hFG f hf ha hdis hcover hhub hr h3
          (fun hh ↦ h34 (h4r.trans hh).symm) E hE
    obtain ⟨J,hJ,hJc⟩ := hlift
    apply hfail
    refine ⟨J,hJ,?_⟩
    simp only [Fintype.card_fin,ceil_half]
    omega

end Erdos583ButterflySmoothingReductionDevelopment
