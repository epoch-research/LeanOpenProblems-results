import Submission.RunCompressionData

/-! Two-stage compression of run families whose carrier walks meet only at a
retained vertex. This does not require separating shortcut owners. -/
namespace Erdos583TwoRunCompressionDevelopment
open SimpleGraph Erdos583Work Erdos583Work.BridgeGlue
open Erdos583CycleRunIntervalsDevelopment Erdos583PrivatePathExpansionDevelopment
open Erdos583RunCompressionDataDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false
variable {V : Type*} {G : SimpleGraph V}

lemma partition_transport {F H : SimpleGraph V} {m : ℕ} (he : F=H)
    (h : ∃ D : Finset F.Subgraph, GoodDecomposition F D ∧ D.card ≤ m) :
    ∃ D : Finset H.Subgraph, GoodDecomposition H D ∧ D.card ≤ m := by
  subst H
  exact h

lemma two_run_partition [Fintype V] {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {a b c d r : V} (W : G.Walk a b) (Q : G.Walk c d) (S : Set V) (hr : r ∉ S)
    (hinter : ∀ z ∈ W.support, z ∈ Q.support → z=r)
    (hw : RunConditions W S) (hq : RunConditions Q S)
    (H : SimpleGraph V) (hH : H.support ⊆ Sᶜ)
    (hfW : ∀ p ∈ runs W S, ¬H.Adj (runStart W p) (runFinish W p))
    (hfQ : ∀ p ∈ runs Q S, ¬H.Adj (runStart Q p) (runFinish Q p))
    (hc : SupportConnected ((H ⊔ arcs (runs W S) (runPath W)) ⊔ arcs (runs Q S) (runPath Q)))
    (hsize : Sᶜ.ncard < n) :
    ∃ D : Finset ((H ⊔ arcs (runs W S) (runPath W)) ⊔ arcs (runs Q S) (runPath Q)).Subgraph,
      GoodDecomposition _ D ∧ D.card ≤ ⌈(Sᶜ.ncard : ℚ)/2⌉₊ := by
  let A := arcs (runs W S) (runPath W)
  let B := arcs (runs Q S) (runPath Q)
  let X := chords (runs W S) (runStart W) (runFinish W)
  let Y := chords (runs Q S) (runStart Q) (runFinish Q)
  have hHB : (H ⊔ B).support ⊆ (W.toSubgraph.verts ∩ S)ᶜ := by
    rintro z ⟨v,hz|hz⟩ hzS
    · exact hH ⟨v,hz⟩ hzS.2
    · have hzQ := Q.mem_verts_toSubgraph.mp (run_arcs_support Q S ⟨v,hz⟩)
      have hzr := hinter z (W.mem_verts_toSubgraph.mp hzS.1) hzQ
      exact hr (hzr ▸ hzS.2)
  have hHX : (H ⊔ X).support ⊆ Sᶜ := by
    rintro z ⟨v,hz|hz⟩
    · exact hH ⟨v,hz⟩
    · exact run_chords_outside W S ⟨v,hz⟩
  have hHX' : (H ⊔ X).support ⊆ (Q.toSubgraph.verts ∩ S)ᶜ := fun z hz hh ↦ hHX hz hh.2
  have hfHB (p : RunIndex W) (hp : p ∈ runs W S) : ¬(H ⊔ B).Adj (runStart W p) (runFinish W p) := by
    rintro (hh|hh)
    · exact hfW p hp hh
    · have haQ := Q.mem_verts_toSubgraph.mp (run_arcs_support Q S ⟨_,hh⟩)
      have hbQ := Q.mem_verts_toSubgraph.mp (run_arcs_support Q S ⟨_,hh.symm⟩)
      exact hw.ne p hp ((hinter _ (W.getVert_mem_support _) haQ).trans
        (hinter _ (W.getVert_mem_support _) hbQ).symm)
  have hfHX (p : RunIndex Q) (hp : p ∈ runs Q S) : ¬(H ⊔ X).Adj (runStart Q p) (runFinish Q p) := by
    rintro (hh|hh)
    · exact hfQ p hp hh
    · have haW := W.mem_verts_toSubgraph.mp (run_chords_support W S ⟨_,hh⟩)
      have hbW := W.mem_verts_toSubgraph.mp (run_chords_support W S ⟨_,hh.symm⟩)
      exact hq.ne p hp ((hinter _ haW (Q.getVert_mem_support _)).trans
        (hinter _ hbW (Q.getVert_mem_support _)).symm)
  have he1 : (H ⊔ B) ⊔ A=(H ⊔ A) ⊔ B := by ac_rfl
  have hc1 : SupportConnected ((H ⊔ B) ⊔ X) := hw.connected W S (H ⊔ B) hHB (he1.symm ▸ hc)
  have he2 : (H ⊔ B) ⊔ X=(H ⊔ X) ⊔ B := by ac_rfl
  have hc2 : SupportConnected ((H ⊔ X) ⊔ Y) := hq.connected Q S (H ⊔ X) hHX' (he2 ▸ hc1)
  have hJ : ((H ⊔ X) ⊔ Y).support ⊆ Sᶜ := by
    rintro z ⟨v,hz|hz⟩
    · exact hHX ⟨v,hz⟩
    · exact run_chords_outside Q S ⟨v,hz⟩
  have hJcard := Set.ncard_le_ncard hJ
  obtain ⟨D,hD,hDc⟩ := LowDegreeAdjacency.smaller_orders_on_support hsmall ((H ⊔ X) ⊔ Y) hc2 (by omega)
  obtain ⟨E,hE,hEc⟩ := hq.expand Q S (H ⊔ X) hHX' hfHX D hD
  obtain ⟨E',hE',hE'c⟩ := partition_transport he2.symm ⟨E,hE,hEc⟩
  obtain ⟨F,hF,hFc⟩ := hw.expand W S (H ⊔ B) hHB hfHB E' hE'
  apply partition_transport he1
  refine ⟨F,hF,?_⟩
  have hh := hFc.trans hE'c
  rw [ceil_half] at hDc ⊢
  omega

end Erdos583TwoRunCompressionDevelopment
